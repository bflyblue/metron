{-# LANGUAGE PatternSynonyms #-}

-- | Property tests over generated programs.
module Lang.Properties (
  propertyTests,
) where

import Data.Maybe (catMaybes, fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T (unpack)
import Gen (exprDepth, genProgram, instanceOf)
import Lang.Common (Source (..), annotations, timedForAllShow)
import Metron.Builtin (pattern BoolT, pattern ListT, pattern TupleT)
import Metron.Core (
  Alt (Alt),
  Nat (Z),
  Term (App, Case, Con, Lam, Let, Pack, Pow, PrimApp, Proj),
  Vec (VNil),
  alphaEq,
 )
import Metron.Desugar (
  desugarClosed,
  noResolver,
  renderDesugarError,
 )
import Metron.Dimension (
  Dim,
  DimAtom (Base, DVar),
  Spelling (Unicode),
  dimAtoms,
  dimDiv,
  dimFromAtoms,
  isDimOne,
  renderDim,
 )
import Metron.Eval (
  EvalError (
    BadCycleIndex,
    DivideByZero,
    Internal,
    UnknownRef,
    Unsupported
  ),
  RuntimeOf (Runtime),
  defaultConfig,
  evalClosed,
 )
import Metron.Hash (hashTerm)
import Metron.Infer (TypeError (..), elaborateClosed, unifyDimensions)
import Metron.Limits (defaultLimits, newBudget, rootContext)
import Metron.Parser (parseExpr)
import Metron.Pretty (renderTerm, renderTermIn)
import Metron.Scalar (Members (Range))
import Metron.Syntax qualified as S (
  Expr (Expr),
  Name (Name),
  Node (
    App,
    BinOp,
    Bool,
    If,
    Lam,
    Let,
    Neg,
    Num,
    Pow,
    Proj,
    Var,
    Vec
  ),
  Op (
    Add,
    And,
    Div,
    Dot,
    EDiv,
    EMul,
    Eq,
    Ge,
    Gt,
    Le,
    Lt,
    Ne,
    Or,
    Outer,
    Sub
  ),
  Pos (Pos),
  Span (Span),
 )
import Metron.TCore (
  TAlt (TAlt),
  TTerm (
    TApp,
    TCase,
    TCon,
    TLam,
    TLet,
    TPack,
    TPow,
    TPrimApp,
    TProj,
    TSample,
    TTyApp,
    TTyLam
  ),
  lintClosed,
 )
import Metron.Type (
  Scheme (..),
  Shape (..),
  Type (
    TChart,
    TData,
    TFun,
    TOver,
    TPoint,
    TTensor,
    TUnit,
    TVar
  ),
  noLookup,
  renderScheme,
  renderType,
 )
import Support.Render (render)
import Test.Tasty (TestName, TestTree, localOption, mkTimeout, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)
import Test.Tasty.Options (IsOption (parseValue))
import Test.Tasty.QuickCheck (
  Arbitrary (arbitrary),
  Gen,
  Property,
  QuickCheckReplay,
  QuickCheckTests (QuickCheckTests),
  Testable (property),
  choose,
  classify,
  counterexample,
  cover,
  discard,
  elements,
  forAllShow,
  frequency,
  label,
  listOf,
  oneof,
  tabulate,
  testProperty,
  vectorOf,
  (.&&.),
  (===),
 )
import Traversal (blankHints)

-- Properties ----------------------------------------------------------------------
--
-- Random surface programs are pushed through the whole pipeline. These pin
-- the invariants of core.md §9: whatever inference accepts, lint accepts;
-- printed Core re-parses to an alpha-equivalent term; hashes ignore hints;
-- evaluation of a linted term never reports an internal error.

noSpan :: S.Span
noSpan = S.Span (S.Pos 1 1) (S.Pos 1 1)

mk :: S.Node -> S.Expr
mk = S.Expr noSpan

{- | A random expression over a scope of bound names. Literals are small
integers and halves so that printed numbers re-parse exactly.
-}
genExpr :: [Text] -> Int -> Gen S.Expr
genExpr scope size
  | size <= 0 = leaf
  | otherwise =
      frequency
        [ (3, leaf)
        , (3, binary)
        ,
          ( 2
          , do
              n <- name
              b <- genExpr (n : scope) (size - 1)
              pure (mk (S.Lam [S.Name noSpan n] b))
          )
        , (2, mk <$> (S.App <$> sub <*> sub))
        ,
          ( 2
          , do
              n <- name
              e <- sub
              b <- genExpr (n : scope) (size - 1)
              pure (mk (S.Let (S.Name noSpan n) [] e b))
          )
        , (1, mk <$> (S.If <$> sub <*> sub <*> sub))
        , (1, mk . S.Neg <$> sub)
        ,
          ( 1
          , do
              k <- choose (2, 3)
              mk . S.Vec <$> vectorOf k sub
          )
        ,
          ( 1
          , do
              k <- choose (2, 3)
              i <- choose (0, k - 1)
              es <- vectorOf k sub
              pure (mk (S.Proj (mk (S.Vec es)) i))
          )
        , (1, (\e n -> mk (S.Pow e n)) <$> sub <*> choose (0, 3))
        ]
 where
  sub = genExpr scope (size `div` 2)
  name = elements ["x", "y", "z", "f", "g"]
  leaf =
    frequency
      $ [ (4, mk . S.Num . fromInteger <$> choose (-3, 9))
        , (1, mk . S.Num <$> elements [1 / 2, 3 / 2, 1 / 4])
        , (1, mk . S.Bool <$> arbitrary)
        ]
        ++ [(3, mk . S.Var <$> elements scope) | not (null scope)]
  binary = do
    op <-
      elements
        [ S.Add
        , S.Sub
        , S.Outer
        , S.Dot
        , S.EMul
        , S.EDiv
        , S.Div
        , S.Eq
        , S.Ne
        , S.Lt
        , S.Le
        , S.Gt
        , S.Ge
        , S.And
        , S.Or
        ]
    mk <$> (S.BinOp op <$> sub <*> sub)

blindSource :: Source
blindSource = Source (genExpr [] 5) (const discard)

typedSource :: Source
typedSource = Source (snd <$> genProgram) (`counterexample` False)

-- | A program as printed Core, for counterexamples.
showProgram :: S.Expr -> String
showProgram e = case desugarClosed noResolver e of
  Left err -> T.unpack (renderDesugarError err) <> "\n" <> show e
  Right (t, _) -> T.unpack (renderTerm (\_ _ _ -> "#") VNil t)

-- | Desugar and elaborate, handing failures to the source.
withElaborated ::
  Source -> S.Expr -> (Term Z -> ([Scheme], TTerm Z) -> Property) -> Property
withElaborated src e k = case desugarClosed noResolver e of
  Left err -> src.rejected (T.unpack (renderDesugarError err))
  Right (t, _) -> case elaborateClosed noLookup t of
    Left err -> src.rejected ("type error: " <> T.unpack err.message)
    Right r -> k t r

forProgram :: Source -> (S.Expr -> Property) -> Property
forProgram src = timedForAllShow src.programs showProgram

-- | The first invariant of core.md §9: lint gives back inference's schemes.
lintAgreesProperty :: Source -> Property
lintAgreesProperty src = forProgram src $ \e ->
  withElaborated src e $ \_ (schemes, typed) -> lintClosed noLookup typed === Right schemes

-- | The invariants of core.md §9 over programs from one source.
pipelineProperties :: Source -> [TestTree]
pipelineProperties src =
  [ testProperty
      "whatever inference accepts, lint accepts with the same type"
      (lintAgreesProperty src)
  , -- Only well-typed terms: an ill-typed one such as a number applied to
    -- a number has no surface spelling because of the quantity rule, and
    -- `:view` only ever prints stored, checked definitions.
    testProperty "printed Core re-parses to an alpha-equivalent term"
      $ forProgram src
      $ \e ->
        withElaborated src e $ \t _ ->
          let printed = renderTerm (\_ _ _ -> "#") VNil t
           in counterexample (T.unpack printed)
                $ case parseExpr printed
                  >>= either (Left . renderDesugarError) Right . desugarClosed noResolver of
                  Left err -> counterexample (T.unpack err) False
                  Right (t', _) -> counterexample (fromMaybe "" (firstDifference t t')) (alphaEq t t')
  , -- The same in the unicode spelling of `:set unicode on` (design §7.3).
    testProperty "printed Core in unicode re-parses to an alpha-equivalent term"
      $ forProgram src
      $ \e ->
        withElaborated src e $ \t _ ->
          let printed = renderTermIn Unicode (\_ _ _ -> "#") VNil t
           in counterexample (T.unpack printed)
                $ case parseExpr printed
                  >>= either (Left . renderDesugarError) Right . desugarClosed noResolver of
                  Left err -> counterexample (T.unpack err) False
                  Right (t', _) -> counterexample (fromMaybe "" (firstDifference t t')) (alphaEq t t')
  , testProperty "hashes ignore hints"
      $ forProgram src
      $ \e ->
        case desugarClosed noResolver e of
          Left err -> src.rejected (T.unpack (renderDesugarError err))
          Right (t, _) -> hashTerm (blankHints t) === hashTerm t
  , testProperty "the hash is stable across printing"
      $ forProgram src
      $ \e ->
        withElaborated src e $ \t _ ->
          case parseExpr (renderTerm (\_ _ _ -> "#") VNil t)
            >>= either (Left . renderDesugarError) Right . desugarClosed noResolver of
            Left err -> counterexample (T.unpack err) False
            Right (t', _) ->
              counterexample
                (fromMaybe "" (firstDifference t t'))
                (hashTerm t' === hashTerm t)
  , testProperty "evaluating a linted term never reports an internal error"
      $ forProgram src
      $ \e ->
        withElaborated src e $ \_ (_, typed) ->
          let budget = newBudget defaultLimits typed
           in case evalClosed
                defaultConfig
                ( Runtime
                    (const Nothing)
                    (\_ _ _ -> Nothing)
                    (\_ _ _ -> Nothing)
                    (const Nothing)
                    (const Nothing)
                    budget
                    (rootContext budget (Range 0 0))
                )
                typed
                >>= render of
                Left (Internal msg) -> counterexample (T.unpack msg) False
                Left (UnknownRef _) -> property False
                Left (BadCycleIndex _) -> property False
                Left err -> label (evalOutcome err) True
                Right _ -> label "value" True
  , testProperty "inference is deterministic"
      $ forProgram src
      $ \e ->
        case desugarClosed noResolver e of
          Left err -> src.rejected (T.unpack (renderDesugarError err))
          Right (t, _) ->
            fmap fst (elaborateClosed noLookup t)
              === fmap fst (elaborateClosed noLookup t)
  ]
 where
  evalOutcome = \case
    DivideByZero -> "division by zero"
    Unsupported _ -> "not implemented"
    _ -> "other error"

propertyTests :: TestTree
propertyTests =
  testGroup
    "properties"
    [ testGroup "blind programs" (pipelineProperties blindSource)
    , testGroup
        "typed programs"
        ( testProperty
            "the generator's programs have the type they were built for"
            generatorProperty
            : pipelineProperties typedSource
        )
    , localOption (mkTimeout 60_000_000)
        $ testProperty
          "the dimension unifier: a solution solves, a refusal has none (design §4.4)"
          dimensionUnifierProperty
    , -- Seeds that once failed, kept so that they cannot fail again unseen
      -- once the random runs have moved on.
      testGroup
        "replayed seeds"
        [ -- `[[x]] · [2]` with `x` of unknown rank: the default made the
          -- operand a vector instead of keeping its two lengths.
          replayed
            "typed programs: a product's operand keeps the lengths it has"
            "(SMGen 15595120681743185597 18082114794975947591,66)"
            (lintAgreesProperty typedSource)
        ]
    ]

{- | Kennedy's unifier (design §4.4) on random equations @d1 = d2@ of the
free abelian group: when it succeeds its substitution makes the two sides
equal, and when it refuses there is no integer solution. Write @d1 / d2@
as variables to exponents @xᵢ@ and base dimensions to exponents @yⱼ@: a
solution exists exactly when the @yⱼ@ are all 0 if there are no
variables, and otherwise when the gcd of the @xᵢ@ divides every @yⱼ@.
-}
dimensionUnifierProperty :: Property
dimensionUnifierProperty =
  forAllShow ((,) <$> genDim <*> genDim) showEquation $ \(d1, d2) ->
    let delta = dimDiv d1 d2
        xs = [k | (DVar _, k) <- dimAtoms delta]
        ys = [k | (Base _, k) <- dimAtoms delta]
        solvable = case xs of
          [] -> null ys
          _ -> all (\y -> y `mod` foldr1 gcd xs == 0) ys
     in cover 10 solvable "solvable"
          . cover 10 (not solvable) "no solution"
          $ case unifyDimensions d1 d2 of
            Right s ->
              counterexample "the solution does not solve it" (s d1 === s d2)
                .&&. counterexample "a solution where none exists" solvable
            Left err ->
              counterexample
                ("refused one that has a solution: " <> T.unpack err.message)
                (not solvable)
 where
  -- Up to three variables and the base dimensions, small exponents.
  genDim :: Gen Dim
  genDim = dimFromAtoms <$> listOf ((,) <$> atom <*> choose (-6, 6))
  atom = oneof [Base <$> elements [minBound .. maxBound], DVar <$> choose (0, 2)]
  showEquation (d1, d2) = T.unpack (renderDim d1 <> " = " <> renderDim d2)

{- | A property run once, at a seed given as @--quickcheck-replay@ takes
it. A seed that does not parse fails the test rather than running at a
random one.
-}
replayed :: TestName -> String -> Property -> TestTree
replayed name seed prop = case parseValue seed of
  Just replay ->
    localOption (replay :: QuickCheckReplay)
      . localOption (QuickCheckTests 1)
      $ testProperty name prop
  Nothing -> testCase name (assertFailure ("the replay seed does not parse: " <> seed))

{- | The typed generator checks itself: inference succeeds on every program
and the type it was built for is an instance of the inferred scheme.
Coverage is tabulated from the elaborated term, so it reports what
inference saw, not what the generator meant.
-}
generatorProperty :: Property
generatorProperty =
  timedForAllShow
    genProgram
    (\(ty, e) -> T.unpack (renderType ty) <> "\n" <> showProgram e)
    $ \(ty, e) ->
      withElaborated typedSource e $ \_ (schemes, typed) ->
        case schemes of
          [sc] ->
            tabulate "target" [targetKind ty]
              . tabulate "depth" [bucket (exprDepth e)]
              . foldr (\(name, present) k -> classify present name . k) id (features typed)
              $ counterexample
                ( "built for "
                    <> T.unpack (renderType ty)
                    <> ", inferred "
                    <> T.unpack (renderScheme sc)
                )
                (instanceOf sc ty)
          _ -> counterexample "more than one scheme" False
 where
  bucket d
    | d < 5 = "1-4"
    | d < 10 = "5-9"
    | d < 15 = "10-14"
    | d < 20 = "15-19"
    | otherwise = "20+"
  targetKind = \case
    BoolT -> "Bool"
    TData _ _ -> "data"
    TFun _ _ -> "function"
    TPoint _ -> "Point"
    TOver _ _ -> "Diff"
    TUnit _ -> "Unit"
    TChart{} -> "Chart"
    TupleT _ -> "tuple"
    ListT _ -> "list"
    TTensor sh d ->
      ( case rankOf sh of
          0 -> "Num"
          1 -> "Vec"
          2 -> "Mat"
          _ -> "rank 3"
      )
        <> (if isDimOne d then "" else " with a dimension")
    TVar _ -> "variable"

rankOf :: Shape -> Int
rankOf = \case
  SNil -> 0
  SCons _ _ rest -> 1 + rankOf rest
  SVar _ -> 0

{- | What an elaborated program exercises: polymorphic lets, dimensioned
tensors, higher ranks, higher-order functions.
-}
features :: TTerm Z -> [(String, Bool)]
features typed =
  [ ("polymorphic let", polyLets typed > 0)
  , ("dimensioned tensor of rank >= 1", any dimensionedTensor tys)
  , ("dimensioned value", any dimensioned tys)
  , ("rank >= 2", any ((>= 2) . tensorRank) tys)
  , ("higher-order function", any higherOrder tys)
  ]
 where
  tys = annotations typed
  dimensioned = \case
    TTensor _ d -> any isBase (dimAtoms d)
    TFun a b -> dimensioned a || dimensioned b
    _ -> False
  dimensionedTensor = \case
    TTensor (SCons{}) d -> any isBase (dimAtoms d)
    TFun a b -> dimensionedTensor a || dimensionedTensor b
    _ -> False
  isBase = \case
    (Base _, _) -> True
    _ -> False
  tensorRank = \case
    TTensor sh _ -> rankOf sh
    TFun a b -> max (tensorRank a) (tensorRank b)
    _ -> 0
  higherOrder = \case
    TFun (TFun _ _) _ -> True
    TFun _ b -> higherOrder b
    _ -> False

-- | Let binders generalised over at least one variable.
polyLets :: TTerm n -> Int
polyLets = \case
  TLet _ (Forall vs _) e b -> (if null vs then 0 else 1) + polyLets e + polyLets b
  TLam _ _ b -> polyLets b
  TApp f a -> polyLets f + polyLets a
  TCon _ _ as -> sum (map polyLets as)
  TCase s _ alts -> polyLets s + sum [polyLets b | TAlt _ _ b <- alts]
  TPrimApp _ _ as -> sum (map polyLets as)
  TPow b _ -> polyLets b
  TSample _ x -> polyLets x
  TPack _ _ ts -> sum (map polyLets ts)
  TProj t _ -> polyLets t
  TTyLam _ _ b -> polyLets b
  TTyApp b _ -> polyLets b
  _ -> 0

{- | Where two terms stop being alpha-equivalent: the outermost differing
subterms, for counterexamples.
-}
firstDifference :: Term n -> Term n -> Maybe String
firstDifference a b
  | alphaEq a b = Nothing
  | otherwise = case (a, b) of
      (PrimApp p as, PrimApp q bs) | p == q, length as == length bs -> firstOf (zipWith firstDifference as bs)
      (Lam _ x, Lam _ y) -> firstDifference x y
      (App f x, App g y) -> firstOf [firstDifference f g, firstDifference x y]
      (Let _ e x, Let _ f y) -> firstOf [firstDifference e f, firstDifference x y]
      (Con c xs, Con c' ys) | c == c', length xs == length ys -> firstOf (zipWith firstDifference xs ys)
      (Case s xs, Case s' ys)
        | length xs == length ys ->
            firstOf (firstDifference s s' : zipWith altDifference xs ys)
      (Pow x n, Pow y m) | n == m -> firstDifference x y
      (Pack xs, Pack ys) | length xs == length ys -> firstOf (zipWith firstDifference xs ys)
      (Proj x i, Proj y j) | i == j -> firstDifference x y
      _ -> here
 where
  here = Just ("first difference:\n  " <> show a <> "\nvs\n  " <> show b)
  altDifference (Alt c _ x) (Alt c' _ y) = if c == c' && alphaEq x y then Nothing else here
  firstOf ds = case catMaybes ds of
    [] -> here
    d : _ -> Just d

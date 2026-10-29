-- | Surface AST to Core (design §2.9), with a provenance table (§4.7).
--
-- Desugaring is total and local: no step needs type information. Bound
-- variables become de Bruijn indices through a context of names; primitives
-- become saturated 'PrimApp' nodes, eta-expanded when used with too few
-- arguments; operators, sections, composition and the quantity rule all
-- reduce to these. Every Core node records the span of the surface node that
-- produced it, keyed by its path from the root.
module Eval.Desugar
  ( Path
  , Provenance
  , Resolver
  , noResolver
  , DesugarError (..)
  , desugarClosed
  , desugarIn
  , renderDesugarError
  ) where

import Control.Monad (zipWithM)
import Control.Monad.Reader (ReaderT, asks, runReaderT)
import Control.Monad.State.Strict (StateT, modify', runStateT)
import Control.Monad.Trans.Class (lift)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Eval.Core
import Eval.Syntax qualified as S

-- | Child positions from the root of a Core term.
type Path = [Int]

type Provenance = Map Path S.Span

data DesugarError
  = UnknownName S.Span Text
  deriving stock (Eq, Show)

renderDesugarError :: DesugarError -> Text
renderDesugarError = \case
  UnknownName sp n ->
    T.pack (show sp.from.line) <> ":" <> T.pack (show sp.from.col) <> ": unknown name `" <> n <> "`"

-- | How free names resolve to codebase references (hash and optional cycle
-- index). Names bound locally shadow these; these shadow primitives.
type Resolver = Text -> Maybe (Hash, Maybe Int)

noResolver :: Resolver
noResolver _ = Nothing

-- | Paths are built in reverse (innermost first) and reversed when stored.
type M = ReaderT Resolver (StateT Provenance (Either DesugarError))

type Ctx n = Vec n Text

desugarClosed :: Resolver -> S.Expr -> Either DesugarError (Term Z, Provenance)
desugarClosed = (`desugarIn` VNil)

-- | Desugar under a context of already-bound names (innermost first).
desugarIn :: Resolver -> Ctx n -> S.Expr -> Either DesugarError (Term n, Provenance)
desugarIn resolve ctx e = runStateT (runReaderT (desugar [] ctx e) resolve) Map.empty

failWith :: DesugarError -> M a
failWith = lift . lift . Left

record :: Path -> S.Span -> M ()
record path sp = lift (modify' (Map.insert (reverse path) sp))

lookupCtx :: Text -> Ctx n -> Maybe (Fin n)
lookupCtx x = \case
  VNil -> Nothing
  VCons y ys
    | x == y -> Just FZ
    | otherwise -> FS <$> lookupCtx x ys

-- | A name that no user identifier can clash with, for binders the desugarer
-- introduces.
fresh :: Text -> Int -> Text
fresh tag j = "§" <> tag <> T.pack (show j)

desugar :: Path -> Ctx n -> S.Expr -> M (Term n)
desugar path ctx e = do
  record path e.span
  case e.node of
    S.Num r -> pure (Lit (LTensor [] [r]))
    S.Bool b -> pure (Lit (LBool b))
    S.Var x -> headApp path ctx e x []
    S.App f a ->
      let (hd, args) = spine e
       in case hd.node of
            S.Var x | Nothing <- lookupCtx x ctx -> do
              bound <- asks (\resolve -> resolve x)
              case bound of
                -- A codebase name: ordinary application of a reference.
                Just _ -> App <$> desugar (0 : path) ctx f <*> desugar (1 : path) ctx a
                -- A primitive (or unknown): saturation and eta rules apply.
                Nothing -> headApp path ctx hd x args
            _ -> App <$> desugar (0 : path) ctx f <*> desugar (1 : path) ctx a
    S.Lam names body -> lams path ctx e.span names body
    S.Let n params rhs body ->
      Let (Hint n.text)
        <$> lams (0 : path) ctx rhs.span params rhs
        <*> desugar (1 : path) (VCons n.text ctx) body
    S.If c t f ->
      If <$> desugar (0 : path) ctx c <*> desugar (1 : path) ctx t <*> desugar (2 : path) ctx f
    S.BinOp op a b -> case op of
      S.PlusMinus k -> Uncertain k <$> desugar (0 : path) ctx a <*> desugar (1 : path) ctx b
      S.To -> prim "to" [a, b]
      S.Compose ->
        -- f ∘ g  =  \x -> f (g x)
        let x = fresh "c" 0
            var = S.Expr e.span (S.Var x)
         in desugar path ctx (synthLam e.span x (S.Expr e.span (S.App a (S.Expr e.span (S.App b var)))))
      S.Infix f ->
        desugar path ctx (S.Expr e.span (S.App (S.Expr e.span (S.App (S.Expr a.span (S.Var f)) a)) b))
      _ -> prim (opPrim op) [a, b]
    S.Neg a -> prim "neg" [a]
    S.Pow a n -> (`Pow` n) <$> desugar (0 : path) ctx a
    S.SectionL op a ->
      -- (op a)  =  \x -> x op a
      let x = fresh "s" 0
       in desugar path ctx (synthLam e.span x (S.Expr e.span (S.BinOp op (S.Expr e.span (S.Var x)) a)))
    S.SectionR a op ->
      -- (a op)  =  \x -> a op x
      let x = fresh "s" 0
       in desugar path ctx (synthLam e.span x (S.Expr e.span (S.BinOp op a (S.Expr e.span (S.Var x)))))
    -- A bracket literal whose elements are all constants of one shape folds
    -- into a single constant; otherwise it is a construction (core.md §5).
    S.Vec es -> do
      elems <- zipWithM (\i a -> desugar (i : path) ctx a) [0 ..] es
      pure (foldConstant elems)
    S.Proj a i -> (`Proj` i) <$> desugar (0 : path) ctx a
  where
    prim p args = PrimApp p <$> zipWithM (\i a -> desugar (i : path) ctx a) [0 ..] args
    synthLam sp x body = S.Expr sp (S.Lam [S.Name sp x] body)

-- | @[Lit, Lit, …]@ of one shape becomes one 'Lit' of the stacked shape.
foldConstant :: [Term n] -> Term n
foldConstant elems = case traverse constant elems of
  Just ((dims, _) : rest) | all ((== dims) . fst) rest ->
    Lit (LTensor (length elems : dims) (concatMap snd (constants elems)))
  _ -> Pack elems
  where
    constant = \case
      Lit (LTensor dims rs) -> Just (dims, rs)
      _ -> Nothing
    constants = foldr (\e acc -> maybe acc (: acc) (constant e)) []

-- | The head and arguments of an application spine.
spine :: S.Expr -> (S.Expr, [S.Expr])
spine = go []
  where
    go acc e = case e.node of
      S.App f a -> go (a : acc) f
      _ -> (e, acc)

-- | A name in head position applied to arguments: a bound variable, a
-- primitive (saturated, eta-expanded, or over-applied), or unknown.
headApp :: Path -> Ctx n -> S.Expr -> Text -> [S.Expr] -> M (Term n)
headApp path ctx hd x args = case lookupCtx x ctx of
  Just i -> applyAll path ctx (\_ -> pure (Var i)) args
  Nothing -> do
    bound <- asks (\resolve -> resolve x)
    case bound of
      Just (h, idx) -> applyAll path ctx (\_ -> pure (Ref h idx)) args
      Nothing -> case specialForm x of
        Nothing -> failWith (UnknownName hd.span x)
        Just (arity, Builder build)
          | length args == arity -> saturated path ctx build args
          | length args < arity -> eta path ctx hd.span (Builder build) args (arity - length args)
          | otherwise ->
              applyAll path ctx (\p -> saturated p ctx build (take arity args)) (drop arity args)

-- | A node constructor that works in any scope, so that eta-expansion can
-- apply it under the binders it introduces.
newtype Builder = Builder (forall m. [Term m] -> Term m)

-- | Names that build a Core node when saturated: every primitive, plus the
-- surface names of the uncertainty operators (design §2.9).
specialForm :: Text -> Maybe (Int, Builder)
specialForm = \case
  "within" -> Just (2, Builder (\case [a, b] -> Uncertain Bound a b; _ -> error "within: arity"))
  "sigma" -> Just (2, Builder (\case [a, b] -> Uncertain Stat a b; _ -> error "sigma: arity"))
  p -> (\arity -> (arity, Builder (PrimApp p))) <$> primArity p

saturated :: Path -> Ctx n -> ([Term n] -> Term n) -> [S.Expr] -> M (Term n)
saturated path ctx build args = build <$> zipWithM (\i a -> desugar (i : path) ctx a) [0 ..] args

-- | Apply a head (built at a given path) to arguments, left-nested.
applyAll :: Path -> Ctx n -> (Path -> M (Term n)) -> [S.Expr] -> M (Term n)
applyAll path ctx mkHead = \case
  [] -> mkHead path
  args -> do
    f <- applyAll (0 : path) ctx mkHead (init args)
    a <- desugar (1 : path) ctx (last args)
    pure (App f a)

-- | Eta-expand a primitive applied to too few arguments:
-- @add 1@ becomes @\x -> add 1 x@. The supplied arguments are desugared
-- under the new binders; they cannot mention the fresh names, so no shifting
-- is needed.
eta :: Path -> Ctx n -> S.Span -> Builder -> [S.Expr] -> Int -> M (Term n)
eta path0 ctx0 sp (Builder build) args missing = go 0 path0 ctx0
  where
    go :: Int -> Path -> Ctx m -> M (Term m)
    go j path ctx
      | j == missing = do
          supplied <- zipWithM (\i a -> desugar (i : path) ctx a) [0 ..] args
          let vars = [Var v | k <- [0 .. missing - 1], Just v <- [lookupCtx (fresh "eta" k) ctx]]
          pure (build (supplied ++ vars))
      | otherwise = do
          record path sp
          Lam (Hint "x") <$> go (j + 1) (0 : path) (VCons (fresh "eta" j) ctx)

-- | Lambdas over a list of parameters, then the body.
lams :: Path -> Ctx n -> S.Span -> [S.Name] -> S.Expr -> M (Term n)
lams path ctx sp names body = case names of
  [] -> desugar path ctx body
  n : ns -> do
    record path sp
    Lam (Hint n.text) <$> lams (0 : path) (VCons n.text ctx) sp ns body

opPrim :: S.Op -> Text
opPrim = \case
  S.Add -> "add"
  S.Sub -> "sub"
  S.Outer -> "outer"
  S.Dot -> "dot"
  S.Cross -> "cross"
  S.EMul -> "emul"
  S.EDiv -> "ediv"
  S.Div -> "div"
  S.Eq -> "eq"
  S.Ne -> "ne"
  S.Lt -> "lt"
  S.Le -> "le"
  S.Gt -> "gt"
  S.Ge -> "ge"
  S.And -> "and"
  S.Or -> "or"
  S.To -> "to"
  S.PlusMinus _ -> "uncertain"
  S.Compose -> "compose"
  S.Infix n -> n

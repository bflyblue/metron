{-# LANGUAGE PatternSynonyms #-}

-- | Helpers the topic modules share: building terms, running sessions, fixtures.
module Lang.Common (
  num,
  bool,
  ifT,
  prim2,
  (+.),
  (-.),
  (*.),
  (/.),
  (==.),
  (<.),
  v0,
  v1,
  v2,
  h,
  Defs,
  elaborateDefs,
  run,
  toks,
  parseShape,
  Tree (..),
  shape,
  desugarText,
  evalText,
  runLines,
  startsWith,
  expecting,
  lastN,
  typeOfText,
  encloses,
  Source (..),
  caseLimit,
  timedForAllShow,
  timedForAll,
  annotations,
  seeded,
  evalU,
  libraryListing,
  librarySize,
  theSeed,
  evalP,
  runLinesP,
  typeOfTextP,
  withTempStore,
  persistLines,
  reload,
  linesIn,
  hashShownAs,
  sessionP,
  completeAt,
  replacements,
  coloured,
  keyword',
  unit',
  type',
  grey',
  red',
  multiline,
  expectError,
  editScript,
  editSession,
  editFileOf,
  replaceOnce,
  edited,
  sessionOf,
  builtinTypeListing,
  astroTypes,
  eciChart,
  lvlhCharts,
  shapeDecl,
  shapeArea,
) where

import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.List (sort)
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Data.Text qualified as T (
  breakOn,
  drop,
  intercalate,
  isInfixOf,
  isPrefixOf,
  length,
  null,
  pack,
  unpack,
 )
import Data.Time.Clock.POSIX (getPOSIXTime)
import Metron.Builtin (boolC, pattern FalseC, pattern TrueC)
import Metron.Codebase (emptyCodebase)
import Metron.Core (
  Alt (Alt),
  Fin (FS, FZ),
  Hash (..),
  Lit (LTensor),
  Nat (S, Z),
  Term (Case, Con, Lit, PrimApp, Var),
  Vec (VNil),
  vecToList,
 )
import Metron.Desugar (
  desugarClosed,
  noResolver,
  renderDesugarError,
 )
import Metron.Driver (
  EditRequest (EditOpen),
  EditScope,
  Session (codebase, config, staging),
  applyEdit,
  editRequest,
  emptySession,
  feed,
  refreshPreferences,
  seededSession,
 )
import Metron.Eval (
  Config (..),
  RuntimeOf (Runtime),
  evalClosed,
 )
import Metron.Eval qualified as E
import Metron.Infer (TypeError (..), elaborateClosed)
import Metron.Lexer (Located (value), Token, tokenize)
import Metron.Limits (defaultLimits, newBudget, rootContext)
import Metron.Parser (parseExpr)
import Metron.Prelude (stdlibNames, stdlibNamespaces)
import Metron.Repl qualified as R (
  Completion (replacement),
  complete,
 )
import Metron.Scalar (Backend (RationalBackend), Members (Range))
import Metron.Store (
  Seed,
  loadStore,
  openStore,
  stdlibSeed,
  sync,
 )
import Metron.Syntax qualified as S (
  ChartClauses (generators, origin, parent, spin, step),
  Expr (node),
  Name (text),
  Node (
    App,
    Ascribe,
    BinOp,
    Bool,
    CaseOf,
    ChartForm,
    FieldOf,
    FromTo,
    If,
    Labelled,
    Lam,
    Let,
    List,
    Neg,
    Num,
    Pow,
    Proj,
    Record,
    SectionL,
    SectionR,
    Slice,
    Tuple,
    UnitBody,
    UnitSyntax,
    Var,
    Vec
  ),
  Op,
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
  Arg (AType),
  Scheme (..),
  Type,
  TypeLookup (TypeLookup),
 )
import Support.Render (render)
import System.Directory (
  createDirectoryIfMissing,
  getTemporaryDirectory,
  removePathForcibly,
 )
import System.FilePath ((</>))
import Test.Tasty.HUnit (Assertion, assertFailure, (@?))
import Test.Tasty.QuickCheck (
  Gen,
  Property,
  Testable,
  forAllShow,
  within,
 )

-- Term-building helpers -------------------------------------------------

num :: Rational -> Term n
num r = Lit (LTensor ([], [r]))

bool :: Bool -> Term n
bool b = Con (boolC b) []

-- | An if, as the desugarer writes it: a case on Bool in canonical order.
ifT :: Term n -> Term n -> Term n -> Term n
ifT c t e = Case c [Alt FalseC VNil e, Alt TrueC VNil t]

prim2 :: Text -> Term n -> Term n -> Term n
prim2 p a b = PrimApp p [a, b]

(+.), (-.), (*.), (/.), (==.), (<.) :: Term n -> Term n -> Term n
(+.) = prim2 "add"
(-.) = prim2 "sub"
(*.) = prim2 "outer"
(/.) = prim2 "div"
(==.) = prim2 "eq"
(<.) = prim2 "lt"
infixl 6 +., -.
infixl 7 *., /.
infix 4 ==., <.

v0 :: Term (S n)
v0 = Var FZ

v1 :: Term (S (S n))
v1 = Var (FS FZ)

v2 :: Term (S (S (S n)))
v2 = Var (FS (FS FZ))

-- Codebase stand-in: hashes are just labels here. Definitions are elaborated
-- in order, so later ones may reference earlier ones.
h :: ByteString -> Hash
h = Hash

type Defs = [(Hash, Term Z)]

elaborateDefs :: Defs -> Either Text [(Hash, ([Scheme], TTerm Z))]
elaborateDefs = go []
 where
  go acc [] = Right (reverse acc)
  go acc ((k, t) : rest) = do
    (schemes, typed) <-
      first (("type error: " <>) . (.message)) (elaborateClosed (typesIn acc) t)
    _ <- first ("lint: " <>) (lintClosed (typesIn acc) typed)
    go ((k, (schemes, typed)) : acc) rest
  typesIn acc = TypeLookup (\k -> fst <$> lookup k acc) (const Nothing)

{- | Elaborate, lint, evaluate and render a closed term against some
definitions. Type errors, lint failures and evaluation errors all come
back as text.
-}
run :: Defs -> Term Z -> Either Text Text
run defs t = do
  elaborated <- elaborateDefs defs
  let typesOf = TypeLookup (\k -> fst <$> lookup k elaborated) (const Nothing)
      typedOf k = snd <$> lookup k elaborated
  (_, typed) <-
    first (("type error: " <>) . (.message)) (elaborateClosed typesOf t)
  _ <- first ("lint: " <>) (lintClosed typesOf typed)
  let budget = newBudget defaultLimits typed
  v <-
    first
      (T.pack . show)
      ( evalClosed
          defaultConfig
          ( Runtime
              typedOf
              (\_ _ _ -> Nothing)
              (\_ _ _ -> Nothing)
              (const Nothing)
              (const Nothing)
              budget
              (rootContext budget (Range 0 0))
          )
          typed
      )
  first (T.pack . show) (render v)

-- Lexer ----------------------------------------------------------------------

toks :: Text -> Either Text [Token]
toks src = map (.value) <$> tokenize src

-- Parser ---------------------------------------------------------------------

-- | Parse and strip spans so that structure can be compared.
parseShape :: Text -> Either Text Tree
parseShape src = shape <$> parseExpr src

data Tree
  = N Rational
  | B Bool
  | V Text
  | L [Text] Tree
  | A Tree Tree
  | Lt Text [Text] Tree Tree
  | I Tree Tree Tree
  | O S.Op Tree Tree
  | Ng Tree
  | P Tree Integer
  | SL S.Op Tree
  | SR Tree S.Op
  | Vc [Tree]
  | Lb Text Tree
  | Pj Tree Int
  | Sl Tree Int Int
  deriving stock (Eq, Show)

shape :: S.Expr -> Tree
shape e = case e.node of
  S.Num r -> N r
  S.Bool b -> B b
  S.Var x -> V x
  S.Lam ns b -> L (map (.text) ns) (shape b)
  S.App f a -> A (shape f) (shape a)
  S.Let n ps r b -> Lt n.text (map (.text) ps) (shape r) (shape b)
  S.If c t f -> I (shape c) (shape t) (shape f)
  S.BinOp o a b -> O o (shape a) (shape b)
  S.Neg a -> Ng (shape a)
  S.Pow a n -> P (shape a) n
  S.SectionL o a -> SL o (shape a)
  S.SectionR a o -> SR (shape a) o
  S.Vec es -> Vc (map shape es)
  S.Labelled l a -> Lb l (shape a)
  S.Tuple es -> Vc (map shape es)
  S.List es -> Vc (map shape es)
  S.CaseOf s _ -> shape s
  S.Proj a i -> Pj (shape a) i
  S.Slice a k i -> Sl (shape a) k i
  S.FieldOf a f -> A (shape a) (V f)
  S.Record hd fs -> foldl (\acc (n, x) -> A acc (A (V n.text) (shape x))) (shape hd) fs
  S.Ascribe a _ -> shape a
  S.ChartForm cl ->
    foldl
      (\acc x -> A acc (shape x))
      (shape cl.parent)
      (catMaybes [cl.origin, cl.step, cl.generators, cl.spin])
  S.FromTo v c c1 -> A (A (shape v) (shape c)) (shape c1)
  S.UnitBody a -> shape a
  S.UnitSyntax a -> shape a

-- Desugar ---------------------------------------------------------------------

desugarText :: Text -> Either Text (Term Z)
desugarText src = do
  e <- parseExpr src
  either (Left . renderDesugarError) (Right . fst) (desugarClosed noResolver e)

-- End to end ------------------------------------------------------------------

evalText :: Text -> Either Text [Text]
evalText src = snd <$> feed emptySession{config = defaultConfig} src

-- Codebase, scratch and versioning -------------------------------------------------

-- | Feed inputs one at a time, as REPL lines, collecting all output.
runLines :: [Text] -> Either Text [Text]
runLines = go emptySession{config = defaultConfig} []
 where
  go _ acc [] = Right (concat (reverse acc))
  go s acc (l : ls) = do
    (s', outs) <- feed s l
    go s' (outs : acc) ls

startsWith :: Text -> Text -> Bool
startsWith = T.isPrefixOf

-- | Fail on an error, otherwise continue with the outputs.
expecting :: Either Text [Text] -> ([Text] -> Assertion) -> Assertion
expecting r k = either (assertFailure . T.unpack) k r

lastN :: Int -> [a] -> [a]
lastN n xs = drop (length xs - n) xs

-- Types -------------------------------------------------------------------------

typeOfText :: Text -> Either Text Text
typeOfText src =
  runLines [":type " <> src] >>= \case
    [t] -> Right t
    other -> Left (T.pack (show other))

{- | An expression that is @true@ when every component of the dimensionless
tensor @e@ differs from the matching component of @t@ by at most @tol@.
-}
encloses :: Text -> Text -> Text -> Text
encloses tol e t =
  "let d = ("
    <> e
    <> ") - ("
    <> t
    <> ") in vmap (\\x -> if abs x <= "
    <> tol
    <> " then 0 else 1) d == vmap (\\x -> 0) d"

{- | Where property-test programs come from, and what to do with one that
does not typecheck: the blind generator's are discarded, the typed
generator's are failures.
-}
data Source = Source
  { programs :: Gen S.Expr
  , rejected :: String -> Property
  }

{- | How long one generated case may take, in microseconds: far above what
any case normally costs (the whole suite runs in seconds), so that a
pathologically slow case fails, with its input printed, instead of
hanging the suite.
-}
caseLimit :: Int
caseLimit = 10_000_000

{- | 'forAllShow' with 'caseLimit' on every case. The limit sits inside the
quantifier, so a case that runs out of time still prints its input.
-}
timedForAllShow ::
  (Testable p) => Gen a -> (a -> String) -> (a -> p) -> Property
timedForAllShow gen shown k = forAllShow gen shown (within caseLimit . k)

-- | 'timedForAllShow' printing the input with 'show'.
timedForAll :: (Show a, Testable p) => Gen a -> (a -> p) -> Property
timedForAll gen = timedForAllShow gen show

-- | Every type annotation in an elaborated term.
annotations :: TTerm n -> [Type]
annotations = \case
  TPrimApp _ ty as -> ty : concatMap annotations as
  TLam _ ty b -> ty : annotations b
  TApp f a -> annotations f ++ annotations a
  TLet _ (Forall _ ty) e b -> ty : annotations e ++ annotations b
  TCon _ ty as -> ty : concatMap annotations as
  TCase s ty alts ->
    ty
      : annotations s
      ++ concat [map snd (vecToList bs) ++ annotations b | TAlt _ bs b <- alts]
  TPow b _ -> annotations b
  TSample _ x -> annotations x
  TPack _ _ ts -> concatMap annotations ts
  TProj t _ -> annotations t
  TTyLam _ _ b -> annotations b
  TTyApp b arg -> (case arg of AType t -> [t]; _ -> []) ++ annotations b
  _ -> []

-- Prelude ----------------------------------------------------------------------------

{- | A session on a seeded codebase: the library by domain, with its six
default uses stored.
-}
seeded :: Session
seeded = (either (error . T.unpack) id seededSession){config = defaultConfig}

{- | An input in a seeded session after @:use@ of some of the library's
namespaces that are not used by default (@astro@, @physics@), without the
lines the @:use@s print.
-}
evalU :: [Text] -> Text -> Either Text [Text]
evalU spaces src =
  drop (length spaces) <$> runLinesP ([":use " <> n | n <- spaces] ++ [src])

-- | The lines @:ls@ at the root of a fresh codebase gives for the library.
libraryListing :: [Text]
libraryListing =
  [ "namespace " <> ns <> " (" <> T.pack (show (librarySize ns)) <> " names)"
  | ns <- sort stdlibNamespaces
  ]

-- | How many labels the library has under a namespace.
librarySize :: Text -> Int
librarySize ns = length (filter ((ns <> ".") `T.isPrefixOf`) stdlibNames)

-- | What a new store is seeded with.
theSeed :: Either Text Seed
theSeed = stdlibSeed

evalP :: Text -> Either Text [Text]
evalP src = snd <$> feed seeded src

runLinesP :: [Text] -> Either Text [Text]
runLinesP = go seeded []
 where
  go _ acc [] = Right (concat (reverse acc))
  go s acc (l : ls) = do
    (s', outs) <- feed s l
    go s' (outs : acc) ls

typeOfTextP :: Text -> Either Text Text
typeOfTextP src =
  runLinesP [":type " <> src] >>= \case
    [t] -> Right t
    other -> Left (T.pack (show other))

-- | A fresh store directory for the length of a test.
withTempStore :: (FilePath -> IO a) -> IO a
withTempStore k = do
  tmp <- getTemporaryDirectory
  stamp <- getPOSIXTime
  let dir = tmp </> ("metron-test-" <> show (round (stamp * 1000000) :: Integer))
  createDirectoryIfMissing True dir
  r <- k dir
  removePathForcibly dir
  pure r

-- | Feed lines one at a time, persisting after each, as Main does.
persistLines :: FilePath -> [Text] -> IO Session
persistLines dir ls = do
  st <- either (error . T.unpack) id <$> openStore theSeed dir
  let go s [] = pure s
      go s (l : rest) = case feed s l of
        Left err -> error (T.unpack err)
        Right (s', _) -> sync st s.codebase s'.codebase >> go s' rest
  go seeded ls

-- | A session on the store as Main opens it.
reload :: FilePath -> IO (Session, [Text])
reload dir = do
  st <- either (error . T.unpack) id <$> openStore theSeed dir
  (cb, notes) <- loadStore st emptyCodebase
  pure
    ( either
        (error . T.unpack)
        id
        ( refreshPreferences
            emptySession{codebase = cb, staging = cb, config = defaultConfig}
        )
    , notes
    )

-- | The output of lines fed to a session in turn.
linesIn :: Session -> [Text] -> Either Text [Text]
linesIn s0 = go s0 []
 where
  go _ acc [] = Right (concat (reverse acc))
  go s acc (l : rest) = do
    (s', outs) <- feed s l
    go s' (outs : acc) rest

{- | The short hash a prelude or scratch name prints as, for tests that
compare against @:hash@ output without pinning digests.
-}
hashShownAs :: [Text] -> Text -> Text
hashShownAs setup n = case runLinesP (setup ++ [":hash " <> n]) of
  Right outs | Just out <- lastMay outs -> T.drop 1 out
  other -> error ("hashShownAs: " <> show other)
 where
  lastMay xs = if null xs then Nothing else Just (last xs)

-- | The session after feeding lines to one with the prelude.
sessionP :: [Text] -> Either Text Session
sessionP = go seeded
 where
  go s [] = Right s
  go s (l : ls) = feed s l >>= \(s', _) -> go s' ls

-- REPL: completion, unicode entry, colour ---------------------------------------

-- | Complete at the end of a line, as haskeline asks: reversed left text.
completeAt :: Session -> String -> Maybe (String, [R.Completion])
completeAt s line = R.complete s (reverse line, "")

replacements :: Session -> String -> [String]
replacements s line = maybe [] (map (.replacement) . snd) (completeAt s line)

-- | Text in an SGR colour, as "Metron.Repl" paints it.
coloured :: Text -> Text -> Text
coloured code t = "\ESC[" <> code <> "m" <> t <> "\ESC[0m"

keyword', unit', type', grey', red' :: Text -> Text
keyword' = coloured "35"
unit' = coloured "36"
type' = coloured "33"
grey' = coloured "90"
red' = coloured "31"

-- Namespaces (design §7.6) ------------------------------------------------------------

-- | A multi-line input, as a file or continuation lines give it.
multiline :: [Text] -> Text
multiline = T.intercalate "\n"

-- | An error that mentions a text.
expectError :: Either Text [Text] -> Text -> Assertion
expectError r needle = case r of
  Left err ->
    (needle `T.isInfixOf` err)
      @? T.unpack ("expected " <> needle <> " in:\n" <> err)
  Right outs -> assertFailure ("expected an error, got " <> show outs)

-- The :edit round trip (design §7.3) -------------------------------------------------

{- | A codebase to edit: two namespaces, root definitions, a unit, a record
with a field a function uses, a cycle, a @±@ definition, a leaf to move,
and dependents across namespaces.
-}
editScript :: [Text]
editScript =
  [ multiline
      [ "let size = 10"
      , "let trip = 2 km"
      , "let area w h = w * h"
      , "unit furlong = 201.168 m"
      , "namespace orbital"
      , "  data Body = Body {mass :: Num kg, dist :: Num m}"
      , "  let weight b = b.mass * 9.81 m/s^2"
      , "  let earth = Body {mass = 6 kg, dist = 1 km}"
      , "  let x = 3"
      , "  let y = x + 1"
      , "  let spare = 42"
      , "  let jitter = sample (normal 2 0.5)"
      , "  let even n = if n == 0 then true else odd (n - 1)"
      , "  let odd n = if n == 0 then false else even (n - 1)"
      , "namespace mechanics"
      , "  let g0 = 9.80665 m/s^2"
      , "  let fall t = g0 * t^2 / 2"
      , "  let useY = orbital.y * size"
      ]
  , ":add"
  ]

editSession :: IO Session
editSession = either (assertFailure . T.unpack) pure (sessionP editScript)

-- | The file @:edit args@ would open.
editFileOf :: Session -> [Text] -> IO Text
editFileOf s args = case editRequest s args of
  Right (EditOpen _ (Right file) _) -> pure file
  other -> assertFailure ("no file to edit: " <> show other)

-- | The text with the first occurrence of a part replaced, which must be there.
replaceOnce :: Text -> Text -> Text -> IO Text
replaceOnce old new text = case T.breakOn old text of
  (_, rest) | T.null rest -> assertFailure (T.unpack ("no " <> old <> " in:\n" <> text))
  (before, rest) -> pure (before <> new <> T.drop (T.length old) rest)

-- | An edit that must succeed.
edited :: EditScope -> Text -> Session -> IO (Session, [Text])
edited target text s =
  either
    (\err -> assertFailure (T.unpack (err <> "\nin the file:\n" <> text)))
    pure
    (applyEdit target text s)

-- | A session afterSetup some lines, or the test fails.
sessionOf :: [Text] -> IO Session
sessionOf ls = either (assertFailure . T.unpack) pure (sessionP ls)

-- | What @:ls --types@ lists of the library's declarations of the built-in types.
builtinTypeListing :: [Text]
builtinTypeListing =
  [ "structural data Bool = False | True"
  , "False : Bool"
  , "True : Bool"
  , "structural data Distribution d = Normal (Num d) (Num d) | Uniform (Num d) (Num d)"
  , "Normal : forall d. Num d -> Num d -> Distribution d"
  , "Uniform : forall d. Num d -> Num d -> Distribution d"
  , "structural data List a = Nil | Cons a (List a)"
  , "Nil : forall a. {a}"
  , "Cons : forall a. a -> {a} -> {a}"
  , "structural data Pair a b = Pair a b"
  , "Pair : forall a b. a -> b -> (a, b)"
  ]

-- | How @:ls --types@ lists the library's @astro.State@ (design §3.8).

{- | The library's records in @astro@, as @:ls --types@ lists them: a body
of a constant set, the classical elements, a transfer, a body's state.
-}
astroTypes :: [Text]
astroTypes =
  [ "data astro.Body = astro.Body {mu :: Num (m^3/s^2), radius :: Num m, flattening :: Num, j2 :: Num, rate :: Num (rad/s)}"
  , "astro.Body : Num (m^3/s^2) -> Num m -> Num -> Num -> Num (rad/s) -> astro.Body"
  , "data astro.kepler.Elements = astro.kepler.Elements {a :: Num m, e :: Num, i :: Num rad, raan :: Num rad, argp :: Num rad, nu :: Num rad}"
  , "astro.kepler.Elements : Num m -> Num -> Num rad -> Num rad -> Num rad -> Num rad -> astro.kepler.Elements"
  , "data astro.maneuver.Transfer = astro.maneuver.Transfer {dv1 :: Num (m/s), dv2 :: Num (m/s), dv3 :: Num (m/s), tof :: Num s}"
  , "astro.maneuver.Transfer : Num (m/s) -> Num (m/s) -> Num (m/s) -> Num s -> astro.maneuver.Transfer"
  , "data astro.State c n = astro.State {epoch :: Point c, pos :: Vec n m, vel :: Vec n (m/s)}"
  , "astro.State : forall c n. Point c -> Vec n m -> Vec n (m/s) -> astro.State c n"
  ]

-- Fixtures ----------------------------------------------------------------------------

{- | The inertial space and its chart, entered as one input: points on
@eci@, a chart of @GCRS@.
-}
eciChart :: Text
eciChart = multiline ["space GCRS = Vec 3 m", "chart eci on GCRS"]

-- | 'eciChart' and a chart in orbit on it, @lvlh@, turned a quarter.
lvlhCharts :: [Text]
lvlhCharts = [eciChart, "chart lvlh on eci at [7000, 0, 0] km by rotz (90 deg)"]

-- | A sum type with fields of a unit.
shapeDecl :: Text
shapeDecl = "data Shape = Circle (Num m) | Rect (Num m) (Num m)"

-- | A function by cases on 'shapeDecl'.
shapeArea :: Text
shapeArea = "let area s = case s of Circle r -> pi * r^2; Rect w h -> w * h"

-- Exact arithmetic keeps structural language tests independent of IEEE rounding.
defaultConfig :: Config
defaultConfig = E.defaultConfig{backend = RationalBackend, samples = 32}

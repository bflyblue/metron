-- | Primitive type schemes and their specialization to static arguments.
module Metron.Primitive.Types (
  primScheme,
  primSchemeFor,
  StaticArg (..),
) where

import Data.Maybe (fromMaybe)
import Data.Ratio (denominator, numerator)
import Data.Text (Text)
import Metron.Builtin (
  boolT,
  frameDefMoving,
  isAxesDef,
  listT,
  spaceOf,
 )
import Metron.Core (ConRef (..), Hash, Lit (..), componentLimit)
import Metron.Dimension (
  BaseDim (Ang, T),
  dimBase,
  dimDiv,
  dimInv,
  dimMul,
  dimOne,
  dimPow,
  dimVar,
 )
import Metron.Primitive (baseUnit)
import Metron.Type (
  Axis (AAnon, ANamed, AVar),
  Frame (..),
  FrameSlot (FrNamed, FrVar),
  Kind (KAxis, KDim, KFrame, KLen, KShape, KSpace),
  Len (..),
  Scheme (..),
  Shape (SCons, SNil, SVar),
  Space (Space, base, dim, shape),
  SpaceSlot (SpVar),
  Type (TChart, TData, TFun, TOver, TPoint, TTensor, TUnit),
  TypeDef,
  VarId,
  appendShape,
  numD,
  numT,
  spaceLens,
  vecT,
 )

{- | The scheme of each primitive. Quantified variables use small fixed ids;
inference instantiates them, 'lint' matches against them. See core.md
"Operators across ranks" for which are shape-polymorphic, and design §4.3
for the dimension rules.
-}
primScheme :: Text -> Maybe Scheme
primScheme name = case name of
  "add" -> Just (Forall [sv, dv] (TFun sd (TFun sd sd)))
  "sub" -> Just (Forall [sv, dv] (TFun sd (TFun sd sd)))
  "emul" -> Just (Forall [sv, dv, d2v] (TFun sd (TFun sd2 (TTensor s (dimMul d d2)))))
  "ediv" -> Just (Forall [sv, dv, d2v] (TFun sd (TFun sd2 (TTensor s (dimDiv d d2)))))
  -- Division of an amount of any shape by a scalar amount.
  "div" ->
    Just
      ( Forall
          [sv, dv, d2v]
          (TFun sd (TFun (numD d2) (TTensor s (dimDiv d d2))))
      )
  -- outer, dot, eq and ne have constraint types; see 'lintConstrained'.
  "neg" -> Just (Forall [sv, dv] (TFun sd sd))
  "abs" -> Just (Forall [sv, dv] (TFun sd sd))
  "floor" -> num1
  "ceil" -> num1
  "round" -> num1
  "sqrt" -> Just (Forall [dv] (TFun (numD (dimPow 2 d)) (numD d)))
  -- Plane angle is a dimension (design §3.2.11): the circular functions take
  -- radians and their inverses return them.
  "sin" -> mono (TFun angleT numT)
  "cos" -> mono (TFun angleT numT)
  "tan" -> mono (TFun angleT numT)
  "asin" -> mono (TFun numT angleT)
  "acos" -> mono (TFun numT angleT)
  "atan" -> mono (TFun numT angleT)
  "sinh" -> num1
  "cosh" -> num1
  "tanh" -> num1
  "exp" -> num1
  "log" -> num1
  "atan2" -> Just (Forall [dv] (TFun (numD d) (TFun (numD d) angleT)))
  -- Points and charts over frames (design §3.10, F4, F5). A chart's own
  -- declaration is 'primSchemeFor''s: it reads the frame, axes and space it
  -- names. A point is written with coordinates along its frame's axes,
  -- @Coords c@, and two points on one frame are @Diff c@ apart.
  "pointOn" ->
    let (f, vs) = frameVar 20
     in Just (Forall vs (TFun (TChart f) (TFun (TOver f (Just dimOne)) (TPoint f))))
  "pointAdd" ->
    let (f, vs) = frameVar 20
     in Just (Forall vs (TFun (TPoint f) (TFun (TOver f Nothing) (TPoint f))))
  "pointSub" ->
    let (f, vs) = frameVar 20
     in Just (Forall vs (TFun (TPoint f) (TFun (TPoint f) (TOver f Nothing))))
  -- An amount placed on a chart from its origin along its axes (design
  -- §7.7): @[0, 0, 0] c .+ v@, at any shape of space.
  "pointAt" ->
    let (f, vs) = frameVar 20
     in Just (Forall vs (TFun (TChart f) (TFun (TOver f Nothing) (TPoint f))))
  -- A point to a chart of another frame of its space (F5), and from a
  -- configuration of its frame (F7).
  "toChart" ->
    let (f, vs) = frameVar 20
        (f1, vs1) = sibling f
     in Just (Forall (vs ++ vs1) (TFun (TPoint f) (TFun (TChart f1) (TPoint f1))))
  "fromTo" ->
    let (f, vs) = frameVar 20
        (f1, vs1) = sibling f
     in Just
          ( Forall
              (vs ++ vs1)
              (TFun (TPoint f) (TFun (TChart f) (TFun (TChart f1) (TPoint f1))))
          )
  -- An amount along a chart's axes (F10): from the space's base axes, or
  -- from a configuration of a frame, along its leading position. Only the
  -- rotation applies.
  "toAxes" ->
    let (f, vs) = vectorFrameVar 20 Nothing
     in Just
          ( Forall
              (vs ++ [tailV, dTailV])
              ( TFun
                  (TTensor (SCons (spaceLen f) f.space.base tailS) dTail)
                  (TFun (TChart f) (TTensor (SCons (spaceLen f) f.axes tailS) dTail))
              )
          )
  "axesFromTo" ->
    let (f, vs) = vectorFrameVar 20 Nothing
        (f1, vs1) = sibling f
     in Just
          ( Forall
              (vs ++ vs1 ++ [tailV, dTailV])
              ( TFun
                  (TTensor (SCons (spaceLen f) f.axes tailS) dTail)
                  ( TFun
                      (TChart f)
                      (TFun (TChart f1) (TTensor (SCons (spaceLen f) f1.axes tailS) dTail))
                  )
              )
          )
  -- lt, le, gt, ge have instance types; see lintConstrained.
  "and" -> mono (TFun boolT (TFun boolT boolT))
  "or" -> mono (TFun boolT (TFun boolT boolT))
  "not" -> mono (TFun boolT boolT)
  "pi" -> mono numT
  -- An amount shown in a unit (design §3.10, U6).
  "to" -> Just (Forall [sv, dv] (TFun sd (TFun (TUnit d) sd)))
  -- The quantity rule after a unit (design §3.10, U4): a dimensionless
  -- literal of any shape times one unit, an amount.
  "scale" -> Just (Forall [sv, dv] (TFun (TTensor s dimOne) (TFun (TUnit d) sd)))
  -- Internal unit construction from a scalar amount.
  "unit" -> Just (Forall [dv] (TFun (numD d) (TUnit d)))
  -- The wedge product is the general binary product of vectors; the 3D
  -- cross product is `star (wedge a b)` and lives in the prelude. Both
  -- vectors and the matrix are along one axis set (design §3.9).
  "wedge" ->
    Just
      ( Forall
          [nv, dv, d2v, xav]
          ( TFun
              (vecA n xa d)
              (TFun (vecA n xa d2) (matA (n, xa) (n, xa) (dimMul d d2)))
          )
      )
  "star" ->
    Just
      (Forall [dv, xav] (TFun (matA (three, xa) (three, xa) d) (vecA three xa d)))
  "norm" -> Just (Forall [nv, dv, xav] (TFun (vecA n xa d) (numD d)))
  -- Rows and columns swap, each keeping its axes.
  "transpose" ->
    Just
      ( Forall
          [nv, mv, dv, xav, xbv]
          (TFun (matA (n, xa) (m, xb) d) (matA (m, xb) (n, xa) d))
      )
  "inverse" ->
    Just
      ( Forall
          [nv, dv, xav, xbv]
          (TFun (matA (n, xa) (n, xb) d) (matA (n, xb) (n, xa) (dimInv d)))
      )
  -- det : Mat n n d -> Num (d^n) needs the length as an exponent; until that
  -- relation exists, det is on dimensionless matrices. Its rows and
  -- columns may be along two axis sets of one size, as a rotation's are.
  "det" -> Just (Forall [nv, xav, xbv] (TFun (matA (n, xa) (n, xb) dimOne) numT))
  -- Covariance (design §3.5): a square-root factor, the covariance of a
  -- vector's statistical nudges, and a vector with a given covariance.
  -- The factor keeps the rows and the columns of what it factors.
  "cholesky" ->
    Just
      ( Forall
          [nv, dv, xav, xbv]
          (TFun (matA (n, xa) (n, xb) (dimPow 2 d)) (matA (n, xa) (n, xb) d))
      )
  "covariance" ->
    Just
      ( Forall
          [nv, dv, xav]
          (TFun (vecA n xa d) (matA (n, xa) (n, xa) (dimPow 2 d)))
      )
  -- The covariance of two vectors' shared statistical nudges: a joint
  -- covariance's off-diagonal block, in the product of their dimensions,
  -- rows along the first's axes and columns along the second's.
  "crossCovariance" ->
    Just
      ( Forall
          [nv, mv, dv, d2v, xav, xbv]
          ( TFun
              (vecA n xa d)
              (TFun (vecA m xb d2) (matA (n, xa) (m, xb) (dimMul d d2)))
          )
      )
  -- The parts of an enclosure (design §3.2.9), elementwise, in the
  -- operand's dimension.
  "mid" -> Just (Forall [sv, dv] (TFun sd sd))
  "bound" -> Just (Forall [sv, dv] (TFun sd sd))
  "sd" -> Just (Forall [sv, dv] (TFun sd sd))
  "vmap" ->
    Just
      (Forall [sv, dv, d2v] (TFun (TFun (numD d) (numD d2)) (TFun sd (TTensor s d2))))
  -- The positions of a vector as values, [0, 1, …, n-1]: never consumed as
  -- positions, so there is still no computed indexing (design §2.10). The
  -- result is along the argument's axes.
  "indices" ->
    Just (Forall [nv, dv, xav] (TFun (vecA n xa d) (vecA n xa dimOne)))
  -- Elementwise combination of two tensors of one shape, ⊙'s general form.
  "vzipWith" ->
    let d3 = dimVar 5
     in Just
          ( Forall
              [sv, dv, d2v, (5, KDim)]
              ( TFun
                  (TFun (numD d) (TFun (numD d2) (numD d3)))
                  (TFun sd (TFun sd2 (TTensor s d3)))
              )
          )
  -- vmap that also passes each component's multi-index, a vector of
  -- exact naturals as long as the rank: Vec (rank s) is the one use of the
  -- type-level rank (design §4.1). The index is a value, never consumed as
  -- a position (design §2.10); its axes are anonymous, since its positions
  -- are the tensor's axes by number, not any frame's (design §3.9).
  "timap" ->
    Just
      ( Forall
          [sv, dv, d2v]
          ( TFun
              (TFun (vecT (LRank 0 0)) (TFun (numD d) (numD d2)))
              (TFun sd (TTensor s d2))
          )
      )
  -- The matrix exponential (design §3.3): dimensionless in and out, so a
  -- matrix with a unit is refused by the unifier; a map of one axis set
  -- to itself.
  "expm" ->
    Just
      ( Forall
          [nv, xav]
          (TFun (matA (n, xa) (n, xa) dimOne) (matA (n, xa) (n, xa) dimOne))
      )
  -- R applied along every axis of a tensor. The type cannot say that every
  -- length of s is n; the evaluator checks it (design §4.3). Nor can it
  -- say "every axis" over axis sets, so it is for anonymous axes only
  -- (design §3.9); linalg's rotateVec and rotateCov are the typed forms.
  "transformBy" ->
    Just
      ( Forall
          [nv, sv, dv]
          (TFun (matA (n, AAnon) (n, AAnon) dimOne) (TFun sd sd))
      )
  -- A chart's absolute rotation (design §3.8, §3.10 F5): its axes, as
  -- columns along its space's base axes, so rows along the base and
  -- columns along the frame's axes.
  "rotationOf" ->
    let (f, vs) = vectorFrameVar 20 Nothing
     in Just
          ( Forall
              vs
              ( TFun
                  (TChart f)
                  (matA (spaceLen f, f.space.base) (spaceLen f, f.axes) dimOne)
              )
          )
  -- Its absolute angular velocity, the velocity of its origin and its
  -- origin, along its space's base axes (design §3.8): zero for a chart
  -- that does not move. The origin is an amount from the space's base
  -- origin, in the space's dimension.
  "spinOf" ->
    let (f, vs) = vectorFrameVar 20 (Just 3)
     in Just (Forall vs (TFun (TChart f) (baseVec f (dimInv (dimBase T)))))
  "originVelocityOf" ->
    let (f, vs) = vectorFrameVar 20 (Just 3)
     in Just
          (Forall vs (TFun (TChart f) (baseVec f (dimDiv f.space.dim (dimBase T)))))
  "originOf" ->
    let (f, vs) = vectorFrameVar 20 Nothing
     in Just (Forall vs (TFun (TChart f) (baseVec f f.space.dim)))
  -- A vector with anonymous axes, read as along a chart's (design §3.9,
  -- §3.10): a relabelling, no arithmetic.
  "withAxes" ->
    let (f, vs) = vectorFrameVar 20 Nothing
     in Just
          ( Forall
              (vs ++ [d2v])
              ( TFun
                  (TChart f)
                  (TFun (vecA (spaceLen f) AAnon d2) (vecA (spaceLen f) f.axes d2))
              )
          )
  -- A base unit is a unit (design §3.10, U1).
  _ -> case baseUnit name of
    Just b -> mono (TUnit (dimBase b))
    Nothing -> Nothing
 where
  sv = (0, KShape)
  dv = (1, KDim)
  d2v = (2, KDim)
  nv = (3, KLen)
  mv = (4, KLen)
  -- Axis variables (design §3.9): the axes of positions.
  xav = (6, KAxis)
  xbv = (7, KAxis)
  s = SVar 0
  d = dimVar 1
  d2 = dimVar 2
  n = LVar 3 0
  m = LVar 4 0
  xa = AVar 6
  xb = AVar 7
  three = LLit 3
  sd = TTensor s d
  sd2 = TTensor s d2
  -- One position, a vector along it, a matrix of two.
  pos l x = SCons l x SNil
  vecA l x = TTensor (pos l x)
  matA (r, x) (c, y) = TTensor (SCons r x (pos c y))
  -- A vector along a frame's space's base axes.
  baseVec f = vecA (spaceLen f) f.space.base
  -- What an amount converted along a chart's axes carries after its
  -- leading position.
  tailV = (40, KShape)
  dTailV = (41, KDim)
  tailS = SVar 40
  dTail = dimVar 41
  mono = Just . Forall []
  num1 = mono (TFun numT numT)
  angleT = numD (dimBase Ang)

{- | The scheme of a primitive whose type is computed from its literal
arguments (design §4.2), given those arguments ('Nothing' where one is not
a constant). 'Nothing' for every other primitive, and 'Left' when the
literals are not what the desugarer admits. The literal arguments stay
arrows of the scheme, at their own types, so inference and lint count
them like any argument.

@contract i j@, with @a = min i j@ and @b = max i j@, has
@Num -> Num -> Tensor (l0 : … : lb : s) d -> Tensor (…) d@ where @lb@ is
@la@ (one length variable at both positions: the paired lengths are
equal) and the result drops positions @a@ and @b@. @permute [p0, …,
pk-1]@ has @Vec k -> Tensor (l0 : … : lk-1 : s) d -> Tensor (lp0 : … :
lpk-1 : s) d@. @slice k i@ has @Num -> Num -> Tensor (l0 : … : lk-1 : n +
i + 1 : s) d -> Tensor (l0 : … : lk-1 : s) d@: axis @k@ is long enough for
position @i@ and is dropped.

Each position is a length and an axis variable (design §3.9), moved or
dropped with its length: @contract@'s paired positions share both.

A chart's declaration (design §3.10, F3, F10), @mkRoot@ on a space and
@mkChart@ on a parent chart, takes the constructor of the frame type it
mints and, when it turns, that of the axis type it mints, read as
@contract@ reads its positions, so that its frame and axes are those
types' hashes; @mkRoot@'s space is read off the space's declaration, from
the given lookup. Every clause is a list of none or one (the generators
any number), and its type depends on which are written: an omitted step,
origin or spin is the empty list. A chart that mints no frame, a rescaling,
has its parent's frame and axes (F3). The generators and the spin are over
axes of their own: a rotation constructor's are anonymous.
-}
primSchemeFor ::
  (Hash -> Maybe TypeDef) ->
  Text ->
  [Maybe StaticArg] ->
  Maybe (Either Text Scheme)
primSchemeFor defs name statics = case name of
  "mkRoot" -> Just $ case statics of
    [ Just (ConArg (UserCon hf 0))
      , Just (ListArg axesL)
      , Just (ConArg (UserCon hs 0))
      , Just (ListArg step)
      , Just (ListArg origin)
      , Just (ListArg gens)
      , Just (ListArg spin)
      ] -> do
        frameIs hf
        axes <- axesFrom axesL
        sp <-
          maybe
            (Left "mkRoot takes a space a declaration made")
            Right
            (defs hs >>= spaceOf hs)
        let ls = fromMaybe [] (spaceLens sp)
            f = Frame (FrNamed hf) (fromMaybe (if null ls then AAnon else sp.base) axes) sp
            along = TTensor (foldr (`SCons` sp.base) SNil ls) sp.dim
        turning <- turns ls gens spin
        pure
          ( Forall
              turning.vars
              ( foldr
                  TFun
                  (TChart f)
                  [ TData hf []
                  , optional axesL (maybe numT (`TData` []) (firstTag axesL))
                  , TData hs []
                  , optional step (TUnit sp.dim)
                  , optional origin along
                  , turning.gens
                  , turning.spin
                  ]
              )
          )
    _ ->
      Left
        "mkRoot takes the frame a chart declaration mints first: declare the chart with chart"
  "mkChart" -> Just $ case statics of
    [ Just (ListArg frameTagL)
      , Just (ListArg axesL)
      , _
      , Just (ListArg step)
      , Just (ListArg origin)
      , Just (ListArg gens)
      , Just (ListArg spin)
      ] -> do
        mapM_ frameIs (firstTag frameTagL)
        axes <- axesFrom axesL
        let size
              | not (null spin) = Just 3
              | not (null gens) = Just (0 :: Int)
              | otherwise = Nothing
            (parent, parentVars) = case size of
              Just k -> vectorFrameVar 20 (if k == 3 then Just 3 else Nothing)
              Nothing -> frameVar 20
            f =
              Frame
                (maybe parent.slot FrNamed (firstTag frameTagL))
                (fromMaybe parent.axes axes)
                parent.space
            ls = case size of
              Just _ -> [spaceLen parent]
              Nothing -> []
        turning <- if null ls then turns [] gens spin else turns ls gens spin
        pure
          ( Forall
              (parentVars ++ turning.vars)
              ( foldr
                  TFun
                  (TChart f)
                  [ optional frameTagL (maybe numT (`TData` []) (firstTag frameTagL))
                  , optional axesL (maybe numT (`TData` []) (firstTag axesL))
                  , TChart parent
                  , optional step (TUnit parent.space.dim)
                  , optional origin (TOver parent Nothing)
                  , turning.gens
                  , turning.spin
                  ]
              )
          )
    _ ->
      Left
        "mkChart takes the frame a chart declaration mints first: declare the chart with chart"
  _ -> primSchemeForLits name (map (>>= litOf) statics)
 where
  litOf = \case
    LitArg l -> Just l
    _ -> Nothing
  firstTag = \case
    [Just (ConArg (UserCon h 0))] -> Just h
    _ -> Nothing
  -- A clause written is a list of one of its type; one omitted, the empty
  -- list, typed at a number.
  optional clause t = listT (if null clause then numT else t)
  frameIs h = case defs h >>= frameDefMoving of
    Just _ -> Right ()
    Nothing ->
      Left
        ( name
            <> " takes the frame a chart declaration mints first: declare the chart with chart"
        )
  axesFrom = \case
    [] -> Right Nothing
    [Just (ConArg (UserCon h 0))]
      | Just def <- defs h
      , isAxesDef def ->
          Right (Just (ANamed h))
    _ ->
      Left
        ( name
            <> " takes the axes a chart declaration mints: declare the chart with chart"
        )
  -- The generators and the spin: on a space of one axis set, each a
  -- dimensionless matrix over axes of its own, and a spin of three.
  turns ls gens spin = case (ls, null gens, null spin) of
    (_, True, True) -> Right (Turning [] (listT numT) (listT numT))
    ([l], _, _)
      | not (null spin) && l /= LLit 3 && not (isVarLen l) ->
          Left "a spinning chart is on a space of three axes"
      | otherwise ->
          Right
            ( Turning
                ([xbv | not (null gens)] ++ [xcv | not (null spin)])
                (optional gens (matA (l, xb) (l, xb)))
                (optional spin (vecA (LLit 3) xc angularRate))
            )
    _ ->
      Left
        "a chart on a space of numbers has no axes to turn: `by` and `spinning` are for a space of vectors"
  isVarLen = \case
    LVar{} -> True
    _ -> False
  xbv = (7, KAxis)
  xcv = (9, KAxis)
  xb = AVar 7
  xc = AVar 9
  angularRate = dimDiv (dimBase Ang) (dimBase T)
  pos l x = SCons l x SNil
  vecA l x = TTensor (pos l x)
  matA (r, x) (c, y) = TTensor (SCons r x (pos c y)) dimOne

-- | The generators' and the spin's types and variables of a chart declaration.
data Turning = Turning {vars :: [(VarId, Kind)], gens :: Type, spin :: Type}

{- | A frame variable with its companions (design §3.10, F1), numbered from
the given id: its slot, its axes, and its space's slot, shape, dimension
and base axes.
-}
frameVar :: Int -> (Frame, [(VarId, Kind)])
frameVar k =
  ( Frame
      (FrVar k)
      (AVar (k + 1))
      (Space (SpVar (k + 2)) (SVar (k + 3)) (dimVar (k + 4)) (AVar (k + 5)))
  ,
    [ (k, KFrame)
    , (k + 1, KAxis)
    , (k + 2, KSpace)
    , (k + 3, KShape)
    , (k + 4, KDim)
    , (k + 5, KAxis)
    ]
  )

{- | A frame variable on a space of one axis set: of a given number of
axes, or of a length variable.
-}
vectorFrameVar :: Int -> Maybe Int -> (Frame, [(VarId, Kind)])
vectorFrameVar k size =
  ( Frame
      (FrVar k)
      (AVar (k + 1))
      (Space (SpVar (k + 2)) (SCons len AAnon SNil) (dimVar (k + 4)) (AVar (k + 5)))
  , [(k, KFrame), (k + 1, KAxis), (k + 2, KSpace)]
      ++ [(k + 3, KLen) | Nothing <- [size]]
      ++ [(k + 4, KDim), (k + 5, KAxis)]
  )
 where
  len = maybe (LVar (k + 3) 0) LLit size

{- | Another frame of a frame's space (design §3.10, F5): its slot and axes
its own, numbered ten on.
-}
sibling :: Frame -> (Frame, [(VarId, Kind)])
sibling f = case f.slot of
  FrVar k ->
    ( Frame (FrVar (k + 10)) (AVar (k + 11)) f.space
    , [(k + 10, KFrame), (k + 11, KAxis)]
    )
  FrNamed _ -> (f, [])

-- | The length of a frame's space of one axis set.
spaceLen :: Frame -> Len
spaceLen f = case f.space.shape of
  SCons l _ _ -> l
  _ -> LLit 0

{- | A constant argument of a primitive, which 'primSchemeFor' may read: a
literal, a constructor with no fields, or a list literal of such, whose
length is what a chart's clauses say (design §3.10, F10).
-}
data StaticArg = LitArg Lit | ConArg ConRef | ListArg [Maybe StaticArg]
  deriving stock (Eq, Show)

primSchemeForLits :: Text -> [Maybe Lit] -> Maybe (Either Text Scheme)
primSchemeForLits name lits = case name of
  "contract" -> Just $ case lits of
    [Just li, Just lj, _]
      | Just i <- position li
      , Just j <- position lj
      , i /= j ->
          let (a, b) = (min i j, max i j)
              ls = [lenAt (if q == b then a else q) | q <- [0 .. b]]
              kept = [l | (q, l) <- zip [0 ..] ls, q /= a, q /= b]
           in Right
                ( Forall
                    (sv : dv : positionVars [0 .. b - 1])
                    ( TFun
                        numT
                        ( TFun
                            numT
                            (TFun (TTensor (appendShape ls s) d) (TTensor (appendShape kept s) d))
                        )
                    )
                )
    _ -> Left "contract needs two distinct literal natural positions"
  "permute" -> Just $ case lits of
    [Just (LTensor ([k], rs)), _]
      | k >= 1
      , Just ps <- traverse integral rs
      , all (`elem` ps) [0 .. k - 1] ->
          let ls = map lenAt [0 .. k - 1]
           in Right
                ( Forall
                    (sv : dv : positionVars [0 .. k - 1])
                    ( TFun
                        (vecT (LLit k))
                        ( TFun
                            (TTensor (appendShape ls s) d)
                            (TTensor (appendShape (map lenAt ps) s) d)
                        )
                    )
                )
    _ -> Left "permute needs a literal permutation of 0 .. k-1"
  "slice" -> Just $ case lits of
    [Just lk, Just li, _]
      | Just k <- position lk
      , Just i <- position li ->
          -- The sliced axis has a length of at least i + 1, as for a
          -- projection: n + i + 1 with n the variable lenId k.
          let before = map lenAt [0 .. k - 1]
           in Right
                ( Forall
                    (sv : dv : positionVars [0 .. k])
                    ( TFun
                        numT
                        ( TFun
                            numT
                            ( TFun
                                (TTensor (appendShape (before ++ [(LVar (lenId k) (i + 1), axisAt k)]) s) d)
                                (TTensor (appendShape before s) d)
                            )
                        )
                    )
                )
    _ -> Left "slice needs a literal natural axis and position"
  _ -> Nothing
 where
  sv = (0, KShape)
  dv = (1, KDim)
  s = SVar 0
  d = dimVar 1
  -- Position q's length and axis variables, interleaved so that they never
  -- share an id.
  lenId q = 10 + 2 * q
  axisId q = 11 + 2 * q
  axisAt q = AVar (axisId q)
  lenAt q = (LVar (lenId q) 0, axisAt q)
  positionVars qs = [(lenId q, KLen) | q <- qs] ++ [(axisId q, KAxis) | q <- qs]
  position = \case
    LTensor ([], [r]) -> integral r
    _ -> Nothing
  integral r
    | denominator r == 1 && r >= 0 && numerator r < componentLimit =
        Just (fromInteger (numerator r))
    | otherwise = Nothing

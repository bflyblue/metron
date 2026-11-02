# Indexed amounts and exterior algebra

Status: **Open.** This is a proposal, not an adopted specification.
Date: 2026-11-02. Source: review worktree at `5160cd1`, including the uncommitted numerical repairs.
No implementation changes accompany this proposal.

The later adopted [sampling design](montecarlo-first.md) removes affine
propagation and hard running bounds. Its implementation is a separate
prerequisite workstream. References below to affine coefficient behaviour
explain the original motivation, not a requirement to retain that backend.
The structural type proposal remains open.

## Recommendation

Replace `TTensor Shape Dim` with `TAmount Structure Dim`.
A structure describes the linear space of coefficients.
Keep ordinary tensors as one case of that structure.
Add exterior powers as factors in the same structure.

Addition remains one operation on amounts of the same structure and dimension.
Tensor product remains one operation that concatenates factors.
Wedge remains a distinct operation that combines exterior grades over the same vector space.
Points, charts and units remain separate types.

Start with literal exterior grades and polymorphic ambient lengths and axes.
This supports exterior powers of every concrete grade without a general solver for arithmetic on grade variables.
Defer symbolic-grade polymorphism until its inference and generalisation rules are specified.
This is a staged implementation of the proposed design, not a restriction of the mathematics.

## What exists today

| Component | Current mechanism | Consequence |
|---|---|---|
| `Type/Base.hs` | `TTensor Shape Dim`, with lengths and named axes in each shape position | Generalising the structure is a type-language change. |
| `Type/Base.hs` | `Len` is a literal, a variable plus an offset, or a residual rank plus an offset | It cannot express the sum of two independent grades. |
| `Type/Base.hs` | `Scheme = Forall [(VarId, Kind)] Type` | Schemes cannot retain arbitrary constraints. |
| `Infer.hs` | Deferred append, rank, equality, frame and dispatch relations | New relations can wait during inference, but need a policy at generalisation. |
| `Infer.hs`, `settle` | Product shapes default to minimum rank, unresolved rank relations fail | Exterior ambiguity needs a separate policy. |
| `Type/Match.hs` | One-way matching validates scheme instances and signatures | Normalisation must work here as well as in unification. |
| `TCore.hs` | Primitives carry explicit types, with independent relation checks for `outer` and `dot` | Wedge can use the same architecture without operator dictionaries. |
| `Eval.hs` | `VTensor` stores dimensions and a flat scalar buffer | Exterior coefficients need a structure descriptor, not merely buffer dimensions. |
| `Encode.hs`, `Hash.hs` | Type constructors and kind arguments have explicit tags | Types, definitions and stored metadata need updated encodings. |

The existing `add` signature quantifies over a shape and a physical dimension.
The existing `outer` relation concatenates shapes.
The existing `wedge` returns a dense matrix, and `star` consumes a dense 3×3 matrix.
That last representation loses the structural guarantee of alternation.

The current Core comment that calls `add` overloaded is stale relative to its tensor-only signature.
This proposal uses the actual primitive signature and the explicit-Core rule in `core.md`.
It does not use that comment as permission to add ad hoc overloading.

## Structure as a list of factors

A factor is one vector space or one exterior power of it.
An exterior power contains alternating coefficients of a fixed grade.
Grade counts the number of vector directions in each basis element.
An amount stores one physical dimension for all coefficients.

The following is design notation, not proposed parser syntax:

```text
Type       = TAmount Structure Dim | ...existing other cases...
Structure  = SNil | SCons Factor Structure | SVar v | Dense Shape
Factor     = AxisFactor Len Axis | ExteriorFactor GradeLiteral Len Axis

Tensor s d = Amount (ordinary axis factors from s) d
Exterior k n a d = Amount (ext k n a) d
```

`ExteriorFactor` stores only grades of at least two.
A vector-space descriptor consists of its length and axis identity, as existing vectors do.
It is not the existing `Space` record, which can describe a scalar or tensor-valued affine space and fixes a physical dimension.
The coefficient dimension remains independent of this descriptor.

Examples of canonical structures:

```text
Num m                 = Amount [] m
Vec a m               = Amount [AxisFactor n a] m
Mat a b m             = Amount [AxisFactor n a, AxisFactor q b] m
Exterior 2 n a m^2    = Amount [ExteriorFactor 2 n a] m^2
```

A list of factors also represents a tensor whose entries are bivectors.
It avoids a special case for multiplying an ordinary tensor by an exterior value.
A rank-two dense tensor and a bivector remain different structures, even when their coefficient counts coincide.

Keep `Tensor`, `Num`, `Vec` and `Mat` as syntax and printing conventions for ordinary factors.
Introduce `Amount` for structure-polymorphic signatures and `Exterior` for one exterior power.
The public spelling of factor lists remains an open syntax decision.
There is only one internal amount constructor, not parallel legacy tensor and amount types.
`Dense Shape` is a residual embedding, not another runtime representation.
It reduces an empty shape to `SNil` and each known shape position to an `AxisFactor`.
Only an unknown dense shape leaves the embedding unresolved.

## Grade-zero and grade-one normalisation

Normalisation replaces equivalent type descriptions with one canonical description.
Use these rules before type comparison, after substitution, and before encoding:

```text
ext 0 n a = []
ext 1 n a = [AxisFactor n a]
ext k n a = [ExteriorFactor k n a]   when k >= 2
```

A grade-zero value is exactly an ordinary scalar.
A grade-one value is exactly an existing vector, including its named axes.
These are type equalities, not runtime conversions.
No extra wrapper or duplicate representation survives evaluation.

Grade zero deliberately erases its ambient length and axes.
Thus `Exterior 0 3 a m` and `Exterior 0 7 b m` both mean `Num m`.
Equality of these types cannot imply that `a = b` or that `3 = 7`.
This loss of information is called non-injectivity.

A top-grade element is not an ordinary scalar.
For example, `Exterior 3 3 a d` retains its grade and axes despite having one coefficient.
A bivector in two dimensions also retains its structure.
Storage size never determines type equality.

Allow grades above the ambient dimension as zero-dimensional coefficient spaces.
For example, `Exterior 4 3 a d` has no coefficients, but still retains grade 4 and axes `a`.
This makes a wedge above the top grade a typed zero without a special scalar result.
Reject negative grades and lengths, and calculate coefficient counts with overflow-safe integers.

A zero-dimensional ambient vector space creates a further boundary case.
`Exterior 1 0 a d` normalises to `Vec 0 a d`, not to a scalar.
No values become interchangeable merely because they are uniquely zero.

## Operators and their domains

All signatures below describe one operation, not a collection of type-class instances.
`r` and `s` range over structures, and `d` and `e` range over physical dimensions.
`++` describes ordered concatenation of structures.

```text
add   : Amount r d -> Amount r d -> Amount r d
sub   : Amount r d -> Amount r d -> Amount r d
neg   : Amount r d -> Amount r d
outer : Amount r d -> Amount s e -> Amount (r ++ s) (d*e)
div   : Amount r d -> Num e -> Amount r (d/e)
to    : Amount r d -> Unit d -> Amount r d
```

`*` and `⊗` continue to name `outer`.
Scalar multiplication follows from `[] ++ r = r` and `r ++ [] = r`.
The product of two bivectors under `*` is their tensor product, not their wedge or geometric product.
No new scaling operator is necessary.

Wedge has the following mathematical relation:

```text
wedge : Exterior k n a d -> Exterior l n a e
     -> Exterior (k+l) n a (d*e)
```

Its scalar cases use ordinary multiplication or scaling.
A scalar contributes no ambient-space constraint.
Two nonscalar operands must agree on their ambient length and axes.
A product of factors, such as a matrix or a tensor of bivectors, is not itself a homogeneous exterior operand.

Keep `dot`, `contract`, `transpose`, `inverse`, `det` and `expm` on their existing dense tensor domains initially.
An exterior factor is not a bundle of dense tensor positions that contraction can silently consume.
Exterior contraction needs its own specification, including whether it pairs forms with vectors or uses a metric.
It is not necessary to add that operation in the first stage.

Keep componentwise nonlinear operations on dense tensors initially.
This includes `abs`, `emul`, `ediv`, `vmap` and scalar statistical summaries.
Explicit coefficient extraction permits basis-dependent calculations without making them generic exterior operations.
Audit every primitive signature rather than globally replacing every `TTensor` match with `TAmount`.

`.+` and `.-` retain their current point operations.
`Diff c` still reduces to the dense structure prescribed by its space.
A bivector cannot displace a point in an ordinary vector space.
A unit is still not a first-class amount.

## Inference in the first stage

Introduce a structure kind and argument in place of using the dense shape kind for every amount.
Keep a separate dense-shape representation where existing `rank`, `indices` and tensor signatures need it.
An embedding from dense shapes to structures must preserve an unknown dense tail.
Treat this as a restricted residual type expression, like the existing `TOver`, rather than equating dense-shape and arbitrary-structure variables.

This distinction prevents a function restricted to dense tensors from accepting an exterior factor through an unconstrained tail.
General linear operations quantify over arbitrary structures.
Dense operations quantify over shapes and use their structure embedding.
Substitution, free variables, kinds and matching must understand both kinds.

Add inference relations for structure concatenation, dense embedding and exterior multiplication.
Use first-order unification on canonical factors with known grades.
Retain current length and axis unification for each factor.
Do not encode grades as physical dimensions or misuse the offset-only length solver for grade sums.

For a wedge application, inspect the operand structures once they become known:

1. A scalar has grade zero and contributes no ambient descriptor.
2. A single ordinary axis factor has grade one and supplies its length and axes.
3. A single exterior factor supplies its literal grade, length and axes.
4. Any other known structure is rejected.
5. An unknown structure leaves the relation pending.

Once both grades are known, add their integer literals and normalise the result.
Scalar–scalar wedge produces an ordinary scalar with no hidden ambient variable.
Scalar–bivector wedge obtains its ambient descriptor from the bivector alone.
Result information can resolve a relation only when the operand decomposition is unique.

For example, a bivector result alone does not select between grades `(0,2)`, `(1,1)` and `(2,0)`.
Do not default an unknown wedge operand to a scalar or vector.
At generalisation, reject a relation that remains ambiguous and ask for operand annotations.
This intentionally differs from the existing minimum-rank default for tensor product.

A bare `\a b -> a ∧ b` therefore needs a signature that fixes its operand grades in this first stage.
An explicitly vector-typed `cross` can retain the body `\a b -> star (a ∧ b)`.
The current signature markers unify an ascribed type before outer settling, which offers an existing route for this information.
Nested lets settle earlier, so annotations must reach the binding that contains an ambiguous wedge.
Tests must cover this boundary rather than assume that every outer signature reaches every inner binding.

Addition remains fully structure-polymorphic without exterior-specific constraints.
`\x -> x + x` has `forall r d. Amount r d -> Amount r d`.
A function with a known scalar multiplier can also retain its other operand's structure variable because an empty product factor is an identity.
No constraint dictionaries are required for these cases.

The two-sided product of arbitrary unknown structures still needs the existing style of append constraint.
Do not claim a fully structure-polymorphic `\x y -> x * y` unless its unresolved concatenation can appear in a scheme.
In this first stage, retain a documented minimum-structure default for unresolved tensor products, separate from wedge's refusal policy.
Dense embeddings also need a deferred relation when their image is compared with an unknown structure.
An ordinary shape can be recovered from a fully known sequence of axis factors, but never from an exterior factor.

## Symbolic grades are a separate extension

A signature with grade variables `k` and `l` needs an expression for `k+l`.
A general Hodge star needs an expression for `n-k` and a domain condition.
The current `Len`, `Scheme` and scheme matcher do not provide these facilities.
Adding another kind alone cannot solve this problem.

A later extension can introduce natural-number grade expressions and residual `ext` expressions.
Its normaliser must retain `ext k n a` when `k` is unknown.
It must not decompose equality of two such expressions as equality of all their arguments.
Grade zero is a concrete counterexample to that decomposition.

That extension also needs rules for nonnegative arithmetic, ambiguous constraints, scheme generalisation and independent lint validation.
Possible designs are restricted arithmetic relations in qualified schemes or explicit grade witnesses plus sufficiently expressive type functions.
Neither design is selected here.
Literal grades avoid importing a general type-family solver into this first feature.

GHC documents the same inference boundary for non-injective type families.
This is a warning about inverse inference, not a recommendation to reproduce System FC.
See the [GHC type-family documentation](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/type_families.html).

## Hodge star and lost ambient information

Initially retain the current oriented Euclidean 3D operation:

```text
star : Exterior 2 3 a d -> Vec 3 a d
```

This has one domain and one result type.
It rearranges and negates independent coefficients without comparisons or new arithmetic remainders.
The standard library can restore `cross a b = star (a ∧ b)` under a vector signature.

A future full Hodge star needs a metric and orientation.
It must also know the ambient dimension when its input is grade zero.
After normalisation, an ordinary scalar cannot supply that information.
Use an explicit ambient/metric witness for the general operation, rather than recovering a frame from a scalar or guessing 3D.

A chart alone is not automatically such a witness.
Charts include offsets and unit scales, while a Hodge star depends on linear geometry and orientation.
The general operation also needs an explicit convention for vectors versus covectors and metric-dependent physical dimensions.
The first stage retains the existing orthonormal Euclidean convention and coefficient dimensions.

## Coefficients, uncertainty and frames

Store coefficients in ascending basis-index order, for example `(12,13,23)` in 3D.
Each coefficient is an existing backend scalar with its current uncertainty representation.
Do not store both halves of an alternating matrix.
Exterior values of grade two or above need not be decomposable into a single wedge of vectors.
Therefore name the type `Exterior`, not `Blade`.

Wedge multiplies coefficients, counts permutation signs, and omits repeated basis directions structurally.
Structural zeros need no uncertainty comparison.
Hodge star in the initial domain only permutes coefficients and changes signs.
This makes `star (wedge a b)` valid even when coefficient arithmetic loses nonlinear statistical information.

This does not make every algebraic identity numerically provable.
For uncertain vectors, separately evaluated coefficients of `v ∧ v` can still lose cancellation information.
Representation preserves alternation within one exterior value, not arbitrary dependencies between separate evaluations.
Exact coefficient tests can assert identities, while approximate tests must assess enclosure and sample behaviour.
Do not introduce expression-representation equality as evidence of shared uncertainty.

Conversion to a dense alternating tensor expands the coefficients with exact structural signs and zeros.
A checked conversion from a matrix can still fail when uncertainty prevents proving alternation.
A separate explicit projection can compute independent alternating coefficients without that proof.
For rank two, use `(Mij - Mji)/2` for `i < j` and represent the result structurally.

A linear map induces a map on each exterior grade.
For bivectors, coefficient transformations use 2×2 minors of the underlying map.
Grade zero is unchanged and grade one uses the existing vector transformation.
Unit scaling remains an operation on the physical coefficient dimension and must not be applied twice through the frame transform.

Keep frame conversion explicit, with matching source and target axis identities.
An initial named function for an induced exterior map avoids extending `to` dispatch before its rules are specified.
A tensor product containing exterior factors needs a map on each selected factor.
Restrict frame shortcuts to their documented domains instead of silently treating those factors as dense positions.

## Core and runtime impact

No new untyped term constructor is required.
Existing saturated `PrimApp`, `Pack`, `Proj`, `TyLam`/`TyApp` in their respective cores, and data constructors supply the term mechanisms.
New type forms, kinds and primitive relations carry the additional meaning.
Typed Core keeps every primitive instantiation explicit.

The independent linter must re-check canonical structures and each primitive relation.
It must reject a matrix passed to `star`, incompatible wedge axes, incorrect result grades, and forged dense/exterior equivalences.
It must not call the inference solver to decide these cases.
Sharing a small terminating normaliser is reasonable, with separate equation tests and malformed-Core tests.

Replace the runtime tensor descriptor with an amount descriptor that retains factor kinds and coefficient counts.
A flat buffer can remain the coefficient store.
Type application already supplies kinded arguments, but the runtime resolver needs the new structure argument and embedding rules.
An unresolved structure that is needed to allocate a value must fail at the existing ambiguity gate.
Never silently choose a scalar descriptor for an unresolved exterior value.

`Pack` can prepend an ordinary axis factor to any amount structure.
`Proj` can remove that leading ordinary factor.
Neither operation exposes an exterior factor as an ordinary vector of coefficients.
Use a named extraction function for coefficients, with a constructor that restores their declared exterior structure.

Coefficient count is the product of factor sizes, with `choose(n,k)` for an exterior factor.
It belongs to checked allocation, not general type inference.
Apply component, memory and step limits before expansion or coefficient enumeration.
The empty buffer above top grade must retain its type descriptor for printing, dimensions and batch handling.

## Implementation map and compatibility

| Area | Required work |
|---|---|
| `Type/Base.hs`, `Type.hs` | Amount and structure representations, kinds, substitution, normalisation, free variables and rendering |
| `Type/Syntax.hs`, `Type/Match.hs` | Surface aliases, literal grades, dense embedding and scheme matching |
| `Infer.hs` | Structure unification, new pending relations, annotation propagation and ambiguity policy |
| `Primitive/Types.hs`, `TCore.hs` | Operator domains, fixed-grade relations and independent lint rules |
| `Eval.hs`, `Batch.hs`, `Needs.hs`, `Pretty.hs` | Amount descriptors, coefficients, allocation, batches and displayed values |
| `Scalar.hs`, scalar backends | Reuse arithmetic, with no requirement for a new scalar backend |
| `Prelude.hs`, chart construction | Restore cross, convert rotation bivectors explicitly to skew matrices |
| `Encode.hs`, `Hash.hs`, `Store.hs` | Canonical encodings, decoder validation, derived metadata and format version |
| Tests and documents | Inference, lint, algebra, uncertainty, limits, frames and storage |

Existing `rotx`, `roty` and `rotz` produce wedge values used as matrix generators.
After the change, explicitly expand those bivectors before matrix exponentiation and chart construction.
Keep the existing signs and component convention in that conversion.
This is a required integration change, not an optional cleanup.

Untyped primitive calls need not change their byte encoding merely because inferred types change.
However, encoded data definitions include types, and their hashes can change.
Changes to library bodies and referenced type hashes also propagate to dependent hashes.
Use a new store format, rebuild derived data, list affected definitions, and recreate stores from exports.
Do not promise that this change preserves all hashes.

## Validation before adoption

The following are acceptance criteria, not tests already executed.
This proposal changes documentation only.
Implementation begins only after the design is adopted.

| Area | Required evidence |
|---|---|
| Normalisation | Idempotence, substitution compatibility, canonical encoding, grade-zero ambient erasure and grade-one identity |
| Separation | Reject matrix+bivector, point+bivector and addition across named axes or physical dimensions |
| Operators | Scalar tensor products preserve structures, wedge adds grades, ordinary outer products remain distinct |
| Inference | Annotated cross succeeds, ambiguous wedge fails, dense tails cannot absorb exterior factors, nested-let annotations work |
| Lint | Reject forged primitive types, grade results, axis matches and structure arguments independently of inference |
| Exact algebra | Bilinearity, associativity, graded commutativity and repeated-basis zeros against an independent basis oracle |
| Approximate arithmetic | Conservative bounds and statistical diagnostics, no false structural proof from matching enclosures |
| Star | Uncertain wedge inputs succeed, coefficient sign convention agrees with existing cross, matrix inputs fail statically |
| Boundary grades | Zero ambient dimension, grades 0 and 1, top grade, above-top zero, no scalar collapse of a one-coefficient exterior value |
| Frames | Induced maps compose on exact inputs, wedge respects linear maps, reflections have the expected orientation signs |
| Integration | Orbital rotation generators, chart conversions, units and K=1/2/4 sampling retain their specified behaviour |
| Resources | Overflow-safe counts, limits before allocation, empty coefficient spaces, no duplicated dense expansion |
| Storage | Canonical round trips, rejected malformed factor tags/grades/counts, exported source rebuilds |

## Scope to approve

The recommended first stage includes the common amount type, factor structures, literal exterior grades, existing linear operators and the 3D star.
It also includes explicit coefficient/tensor conversion, induced linear maps and the chart-library integration above.
It excludes symbolic-grade polymorphism, arbitrary metrics, mixed-grade multivectors and the geometric product.
Those extensions need separate type and physical-dimension rules.

Mixed grades introduce a specific SI question.
A geometric product of dimensionful vectors has scalar and bivector parts with the same product dimension.
Adding an ordinary displacement directly to a dimensionless scalar remains invalid.
A future multivector design must preserve that distinction instead of assigning units from grade alone.

The remaining syntax decisions are the spelling of structures, coefficient construction, induced maps and the future ambient witness.
These do not require implementation to compare their usability.
The main architectural decision is whether this first stage provides enough grade polymorphism for intended programs.

## References

[GAlgebra's module documentation](https://galgebra.readthedocs.io/en/latest/module-components.html) describes basis-blade coefficients and its metric-aware algebra operations.
The coefficient representation is a useful precedent, not a dependency recommendation.
Its dual conventions are not adopted implicitly here.

[GHC's type-family documentation](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/type_families.html) explains injectivity and inference restrictions.
Metron needs its own smaller rules for the proposed normalisation.
This document does not claim complete inference for arbitrary symbolic grades.

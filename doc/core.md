# Core

The small language in the middle of `eval`. Everything the user writes is
translated into it; everything the implementation does is done to it. This
document says what Core is for, why it is shaped the way it is, what must
stay true of it, and how it is allowed to change. The language design as a
whole is in [design.md](design.md); this is the companion that owns §5.

## Contents

1. Purpose
2. The lesson from GHC
3. Principles
4. Two cores, one meaning
5. The constructor inventory
6. Invariants
7. Changing Core
8. What is coming, and what it will cost
9. Correctness strategy
10. Distance from System FC

---

## 1. Purpose

Core exists so that only one language has to be right.

The surface language (design §2) is rich on purpose: unicode operators,
superscripts, the quantity rule, sections, `where`, projections, named
positions one day. It will keep changing, because it is the part users touch.
If every phase of the implementation read the surface language, every surface
change would ripple through inference, hashing, evaluation, pretty-printing and
the compiler, and each of those would have its own partial understanding of the
sugar. Instead the desugarer translates all of it into Core once, and every
other phase reads Core. A surface change is a desugarer change.

Core also carries the two properties the whole design rests on:

- **Identity.** A definition's content hash is the hash of its Core (design §6).
  Two surface spellings of the same thing are the same definition because they
  desugar to the same Core. The codebase, versioning and propagation all work on
  Core terms, never on text.
- **Meaning.** The evaluator, the type checker and later the compiler define
  what a program does by what its Core does. There is no second semantics for
  the surface language; the surface *means* its desugaring.

## 2. The lesson from GHC

GHC's Core is the clearest precedent. Haskell's surface has grown for thirty
years: type classes, records, pattern guards, view patterns, arrows, GADTs,
type families, do-notation and its many variants. GHC's Core barely moved.
It is an explicitly typed lambda calculus of about ten constructors, System FC,
and every one of those surface features is desugared into it. The optimiser,
the code generators and Core Lint all read only Core.

Simon Peyton Jones has been explicit that this is deliberate and that resisting
additions to Core is most of the work. A new surface feature that can be
desugared into existing Core is a desugarer change and costs the rest of the
compiler nothing. A feature that *cannot* be desugared is treated as a signal
that the language itself has changed in a fundamental way, and it is argued
over at length before Core grows: GADTs and type families were expressed by
adding one thing, coercions, after years of design, rather than by adding a
constructor per feature.

The payoff is correctness. Core Lint is a plain type checker, a few hundred
lines, that re-checks Core after every pass. Because Core is small, Lint is
small and trustworthy, and it has caught a very large share of GHC's own bugs
over the years. A small core is not elegance for its own sake; it is the thing
that makes an independent checker cheap enough to run everywhere.

We adopt the same posture. We are a long way from GHC's scale, which is exactly
why the discipline is affordable now and expensive to retrofit later.

## 3. Principles

1. **Core is minimal.** A constructor is added only when the existing Core
   cannot express something by desugaring. That inability is treated as a
   signal of a real language extension, written up in §7 and §8 before any
   code changes. "It would be more convenient" is not a reason.
2. **Everything is desugared.** Operators, sections, composition, the quantity
   rule, `where`, multi-parameter lambdas, named positions: none of it reaches
   Core. If a feature can be explained as a rewrite into Core, that rewrite is
   its definition.
3. **Core is explicit.** Nothing is implicit, overloaded or inferred inside
   Core. Primitives are saturated, names are resolved to hashes, binding is
   positional. Typed Core goes further: every binder carries its type and
   every use of a polymorphic name says what it is instantiated to.
4. **Core is well-scoped by construction.** The term type is indexed by the
   number of variables in scope, so a dangling variable is a Haskell type
   error, not a runtime one, and the evaluator's environment lookup is total.
5. **Core is nameless.** Binders carry a printing hint that hashing, equality
   and substitution ignore. Alpha-equivalent terms are equal terms. Source
   positions never enter Core; the provenance table (design §4.7) carries them
   beside it.
6. **Typed Core is derived, never authoritative for identity.** The hash is
   of untyped Core. Types, elaboration and anything else computed from a term
   are stored as derived data under that hash and can be recomputed. Adding a
   type feature never changes what a definition *is*.
7. **Everything that reaches storage or evaluation has been linted.** Lint is
   the independent check on elaboration. A lint failure is an internal error
   and is reported as one, never silently stored.

## 4. Two cores, one meaning

There are two representations, and the design is clearer for having both.

**Core** (`Eval.Core`) is untyped. It is what desugaring produces and what gets
hashed. It must be able to hold ill-typed terms, because it is the *input* to
the type checker: `1 + true` is a perfectly good Core term that inference then
rejects with a source position.

**Typed Core** (`Eval.TCore`) is Core after inference and elaboration: System F
with annotated binders, explicit type and length abstraction and application,
and primitives carrying the type they are used at. It is what `lint` checks,
what the evaluator runs, and what a compiler would read.

Elaboration is a function from Core to Typed Core; erasure is a function back,
and erasing an elaborated term gives back the Core it came from up to the
hints. Both cores have the same binding structure and the same constructors
apart from the type forms, so the evaluator for one is the evaluator for the
other with four erasure cases added. We keep two types rather than one with
optional annotations because the invariants differ: Core promises alpha-
equivalence and a canonical encoding; Typed Core promises that lint has
accepted it.

## 5. The constructor inventory

Every constructor earns its place by being something the others cannot
express. Where a constructor is a *special form* that a more general mechanism
would later subsume, that is said, because it marks a place where Core is
larger than it will eventually need to be.

### Core (`Term n`, 14 constructors)

| Constructor | Why it exists | Status |
|---|---|---|
| `Var (Fin n)` | bound variable | fundamental |
| `Ref hash [idx]` | another definition by content hash; the codebase's edge | fundamental |
| `PrimApp name [Term n]` | saturated primitive; the only way to reach arithmetic and the runtime | fundamental |
| `Lit` (a constant tensor: shape plus flat row-major rationals, or a boolean) | constants; a number is the rank-zero case, so there is no separate number literal | fundamental; the boolean alternative is the last special-cased constant and leaves with `If` when `Case` arrives |
| `Lam hint (Term (S n))` | one-parameter abstraction | fundamental |
| `App` | application | fundamental |
| `Let hint e (Term (S n))` | non-recursive, generalising local binding; cannot be `App (Lam …)` because `Let` is where let-polymorphism happens | fundamental |
| `If` | conditional, lazy in both branches; cannot be a primitive because primitives evaluate under call-by-need only argument by argument, and `if` must *select* a branch | special form: becomes `Case` on `Bool` when `Case` arrives |
| `Pow t Integer` | `e ^ n` with a literal exponent, so the dimension of the result is static | special form: stays, because the exponent is syntax, not a value |
| `Noise kind n` | `n` fresh nudges with definition-site identity (design §3.2.4); the identity depends on the node's path, which no primitive can see | special form: stays |
| `Uncertain kind x e` | `x ± e`; expressible as `x + e * noise 1` but kept as a node so identity and `:view` are exact | special form: candidate for removal once `Noise` identity is settled |
| `Pack [Term n]` | construction of a tensor from component terms: `k` tensors of shape `s` become shape `k : s`; a bracket literal whose elements are all constants is folded into `Lit` by the desugarer, so the two never describe the same value | special form: stays, `Tensor` is a built-in type with a shape index no data declaration can express |
| `Proj t i` | component at a literal position, peeling the first length off the shape, checked statically | special form: stays, for the same reason |
| `Cycle (Vec k hint) (Vec k (Term (k + n)))` | `k` mutually recursive definitions hashed as one term (design §6.2) | fundamental for the codebase |

### Typed Core (`TTerm n`, 16 constructors)

The fourteen above with types on `TLam`, `TLet`, `TPrimApp` and `TCycle`, plus
two kinded type forms: `TTyLam v kind body` and `TTyApp body arg`, where the
argument is a type, a length or a shape according to the kind, and a
dimension once dimensions arrive. One pair serves every index kind, so adding a
kind adds no constructor.

### Operators across ranks

Making `Num` the rank-zero tensor raises the question of which primitives work
on every tensor. The answer is decided by whether the operation has one meaning
at every rank:

- **Elementwise, shape-polymorphic**: `+`, `-`, `⊙`, `⊘`, `neg`, `abs`, `vmap`,
  and `==`. One type, `Tensor s -> Tensor s -> Tensor s`, one code path over the
  flat buffer. Scalars are the rank-zero instance of the same path.
- **Products that change rank**: `*` (the tensor product, `s1 ++ s2`) and `·` (the
  contracting product, `s1 ++ s2` after removing the paired index). Scalar
  scaling and plain multiplication are `*` with a rank-zero operand; the dot
  product and matrix multiplication are `·`. Their types need shape
  concatenation, which inference carries as a deferred constraint (design §4.2).
  No overloading: each has exactly one type.
- **Rank-specific**: `×` (`cross`), `norm`, `transpose`, `inverse`, `det`, each
  with a fixed-rank signature; `contract` and `permute` with literal indices are
  roadmap items for ranks above two.
- **Overloaded**: `==` and `/=` only, over tensors and `Bool`, through an
  instance constraint with those two instances. Everything else in the language
  has one type.
- **Scalar only**: `/` takes a scalar divisor; comparisons `< <= > >=`, `floor`,
  `ceil`, `round`, the transcendental functions, `^`, and `±`. A tensor has no
  order, and these would otherwise be ambiguous between elementwise and aggregate
  readings.

### What is deliberately absent

- **`Case` and data constructors.** Nothing in the language needs them yet.
  They arrive with tuples (§8) and will absorb `If` and booleans.
- **Local recursion.** `Let` is non-recursive. Recursion is a top-level affair
  through `Cycle`, which is where hashing needs it. A local recursive helper
  can be a top-level definition.
- **Coercions.** System FC's `Cast` exists for GADTs, type families and
  newtypes. We have none, and dimension equality is decided by normalisation,
  so lint compares normal forms and needs no proof terms.
- **Source positions, names, comments, annotations.** All beside Core, never in
  it.
- **Anything operational**: strictness, unboxing, join points, ticks. Those are
  compiler concerns and belong to a later representation if one is ever needed.

## 6. Invariants

These are the contract between phases. Lint checks the typed ones; the
constructors' types enforce the structural ones; tests pin the rest.

- **Well-scoped.** A `Term n` mentions variables below `n` only. Enforced by
  the GADT.
- **Saturated primitives.** `PrimApp p args` has exactly `primArity p`
  arguments. The desugarer eta-expands; inference and lint reject anything
  else. Consequence: `App` only ever applies a user function.
- **Resolved names.** A `Ref` points at a hash that exists in the codebase
  with stored types. Inference fails on a dangling one.
- **Rationals in lowest terms**, so equal numbers have equal encodings.
- **Alpha-equivalence is equality.** Hints never affect `alphaEq`, hashing or
  evaluation. The pretty-printer may use them freely.
- **Canonical encoding** (design §6.1): one byte tag per constructor, varints,
  de Bruijn indices. The hash is SHA-256 of it. New constructors get new tags
  and never change existing encodings.
- **Cycle shape.** Members are ordered by their placeholder hash (design §6.2),
  bodies live in scope of all members, and the term is reached only through
  `Ref h (Just i)`; a `Cycle` never appears inside an expression.
- **Typed Core lints.** Every binder annotation is correct, every primitive is
  used at an instance of its scheme, every type application has a matching
  abstraction, every `Let` binder's scheme matches its right-hand side, and
  erasing the type forms gives back the Core.
- **Erasure is semantics-preserving.** The evaluator may ignore every type form.

### What the hash depends on

A definition's identity is the hash of its Core. That makes the hash a
function of three things, not one:

1. what the user wrote;
2. the **desugaring rules** that turn it into Core (design §2.9), including
   small canonicalisations such as "negating a constant is a negative
   constant" or "a bracket of constants is one constant";
3. the **canonical encoding** (design §6.1) and the set of primitive names.

Only the first is the user's. The other two are part of the trusted base, and a
change to either re-identifies every stored definition it touches: a definition
containing `-3` had one hash before negative constants were canonical and has
another after. Nothing is persisted yet, so today such a change costs nothing.
Once the codebase lives on disk and iapetus depends on stable hashes, every
desugaring or encoding change is a migration of stored definitions and their
history.

This is the asymmetry that makes a small, stable Core matter: library
definitions can be versioned by the codebase itself, since a new version is a
new hash and the old one stays reachable; primitives, desugaring rules and the
encoding cannot, because they are the ground the hashes stand on. The slogan
"the surface language is free to change" is true of the *phases*, which read
Core and never the surface, and false of the *hashes*, which encode the
translation.

Before persistence lands (design §10, item 6) one of three policies has to be
chosen and written down: freeze the desugaring rules and encoding behind a
version number, with any change being a numbered migration; store the original
source beside each hash so definitions can be re-desugared and re-hashed; or
treat migrations as a routine, tooled operation. Until then, desugaring changes
are made freely but each one is listed in the changelog as a hash-affecting
change.

## 7. Changing Core

Any proposal to add, remove or change a constructor goes through this test
before code:

1. **Can the existing Core express it by desugaring?** If yes, it is a
   desugarer change. Write the rewrite rule in design §2.9 and stop. Most
   surface features end here, and that is the point.
2. **If not, what is the fundamental thing it adds?** Name the capability the
   current Core lacks (first-class choice between alternatives; data with
   structure; a new kind of type). If the answer is "convenience" or
   "performance", the answer to step 1 was wrong.
3. **Write it up here first.** Add the constructor to §5 with its
   justification, its typing rule to the lint contract in §6, its tag to the
   encoding table in design §6.1, and its evaluation rule to design §8.
4. **Can an existing constructor be removed because of it?** `Case` removes
   `If`. A change that makes Core smaller overall is the best kind.
5. **Then implement, in this order:** the constructor; `alphaEq`, `refs`,
   `rewriteRefs`, the encoder; inference and elaboration; lint; the
   evaluator; the pretty-printer. Run the property tests from §9. Nothing is
   stored until lint accepts the new form.
6. **Hash impact.** A new tag never changes the hash of an existing term.
   Changing an existing constructor's encoding does, and so is a codebase
   migration; it needs a reason strong enough to write down.

## 8. What is coming, and what it will cost

Applying the test to the roadmap, in order:

- **Dimensions (design §4).** `Tensor s` becomes `Tensor s δ`. This changes the
  type language, not the term language: no new Core constructor, and since
  variables are already kinded, no new Typed Core form either; `Dim` is one more
  kind with its own unifier.
- **Dictionaries (design §4.2).** The shape-append and equality constraints are
  solved or defaulted today. Keeping an unresolved one in a scheme needs a
  parameter at run time, a dictionary. With data constructors available a
  dictionary is just a record, as in GHC, so this waits for `Case` rather than
  adding `DictLam`/`DictApp` forms of its own. No new Core form either way.
- **Tuples, then lists, then user data types.** This is the one genuine
  extension on the horizon: structured data and first-class choice between
  alternatives, which no desugaring into the current Core can provide. It adds
  `Case` and constructor application, once, and removes `If` and the boolean
  literal. `Vec`, `Mat` and `Proj` stay built in because the length index is
  beyond an ordinary data declaration.
- **Affine arithmetic, units, printing, covariance.** Runtime and prelude work.
  No Core change; `Noise` and `Uncertain` already exist for it.
- **Persistence.** The encoding is the on-disk format already. The decoder
  must reconstruct a well-scoped term from bytes, which is a scope check, not
  a Core change.
- **A compiler.** Reads Typed Core. No Core change; possibly a later, lower
  representation of its own.

So in the foreseeable roadmap Core grows by exactly one mechanism, `Case` with
constructors, and shrinks by one, `If`, with the kinds refactor shrinking Typed
Core as well. That is the shape SPJ's discipline predicts: long stretches where
the surface grows and the core does not.

## 9. Correctness strategy

Core is small so that it can be made correct, and these are the means:

- **Types enforce scope.** The `Fin n` / `Vec n` indexing makes the most common
  interpreter bug, a wrong de Bruijn index, uncompilable.
- **Lint checks elaboration**, independently of inference, on every path into
  storage or evaluation. The two are written separately and must agree.
- **Property tests** over randomly generated programs: whatever inference
  accepts, lint accepts; `renderTerm` output re-parses and desugars to an
  alpha-equivalent term; hashing is stable across that round trip; encoding
  decodes (once the decoder exists) to an alpha-equivalent term; cycle hashes
  are independent of entry order; alpha-equivalent terms hash equal.
  *Known weakness:* the generator builds programs blindly, so about three in
  four are ill-typed and discarded before they reach lint or the evaluator,
  and the survivors skew small and simple. The pass counts are honest about
  what ran, not strong evidence about deep shapes (nested polymorphic lets,
  products inside recursion, dimensioned tensors). The planned fix is a
  type-directed generator that builds each program from a chosen type, so
  every case is well-typed and the type space, now including shapes and
  dimensions, is explored on purpose. Worth doing before affine arithmetic
  adds another kind of value to cover.
- **Unit tests pin the special forms**: laziness of `If` and of `and`/`or`,
  saturation, projection bounds, cycle knot-tying.
- **One place per concern.** Each constructor appears in exactly one `case` in
  each of: `alphaEq`, `refs`, `rewriteRefs`, the encoder, inference, lint, the
  evaluator, the pretty-printer. GHC's `-Wincomplete-patterns` is on, so adding
  a constructor and forgetting a phase is a compile error.
- **The primitive table is part of the trusted base.** Lint checks that a
  primitive is used at an instance of its declared scheme; it cannot know
  whether the scheme itself matches what the evaluator can do. `==` was once
  declared `a -> a -> Bool`, which let two functions be compared: inference
  accepted it, lint agreed, and the evaluator hit an internal error. The
  invariant "lint accepts, therefore evaluation cannot raise a type error" holds
  only if every scheme in `primScheme` is at most as general as the primitive's
  runtime implementation. Each scheme is reviewed against its implementation
  when either changes, and the soundness tests pin the cases that have bitten.

## 10. Distance from System FC

| | System FC | Ours |
|---|---|---|
| Term constructors | about 10 | 15 untyped, 19 typed |
| Typing | explicit, Lint-checked | explicit, lint-checked |
| Polymorphism | type abstraction and application | same, plus lengths; dimensions next |
| Data | `case` over constructors; `Bool` is data | built-in `if`, vectors, matrices; `Case` pending |
| Recursion | `let rec`, local | top-level `Cycle` only |
| Coercions | `Cast` with proofs | none needed |
| Kinds | full kind system | fixed kinds: type, length, soon dimension |
| Identity | none | content hash of untyped Core |

Structurally we are GHC's Core as it stood before coercions, with built-in data
where FC uses `case`, and with content addressing that FC never needed. The
gap that matters is `Case`; the rest is intended.

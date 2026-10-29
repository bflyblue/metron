# Changelog

## Unreleased

- Core term language (well-scoped, saturated primitives) and a direct
  evaluator over it (design §5.1, §8).
- Lexer with the unicode spellings and layout rule, parser over a token
  stream, desugarer with provenance, decimal printing, and the `eval` CLI
  (one-shot, file, stdin, minimal REPL).
- Canonical encoding and SHA-256 content hashing, the in-memory codebase
  (terms, names, history), binding groups with SCC analysis and Unison-style
  cycle hashing, so recursion and mutual recursion work, and the REPL
  commands `:hash`, `:names`, `:history`, `:view`, `:dependents`.
- Unison-style scratch: definitions are pending until `:add` or `:update`;
  `:update` propagates new versions to dependents in dependency order,
  `:upgrade` does so on demand, plus `:todo`, `:scratch`, `:forget`, `:edit`,
  `:alias`, `:unname`. Propagation is unconditional until inference exists.
- REPL `:load file` and `eval -i` (REPL loop over piped stdin, for scripting).
- Hindley-Milner inference over Core with let-polymorphism and length-indexed
  `Vec`/`Mat` (projection gives `Vec (n + k)` lower bounds); types stored in
  the codebase; static type errors with source excerpts; `:type`; `:update`
  and `:upgrade` now leave dependents that no longer typecheck on their old
  version and say why. No dimensions or operator overloading yet.
- Typed Core: System F style terms with annotated binders and explicit type
  and length abstraction/application, produced by elaboration, checked by a
  Core-Lint-style `lint` before storage or evaluation, and run by the
  evaluator (which erases the type forms). `:core name` prints it.
- Kinded type variables (`Type`, `Len`, `Shape`) with one abstraction and one
  application form in Typed Core; `Vec`/`Mat` replaced by `Tensor shape`, with
  `Num` the rank-zero case; `Lit` is a constant tensor and `Pack` a
  construction, `MatLit` removed; `+ - neg abs vmap ==` are shape-polymorphic;
  `dot`, `cross`, `transpose` and `vmap` evaluate; tensors are flat row-major
  buffers at runtime. `:lint name`.
- Products as first-class tensor operators, each with one type: `*`/`⊗`
  (tensor product, covering scalar scaling), `·`/`@` (contracting product:
  dot, matrix-vector, matrix-matrix), `×`/`><` (cross), `⊙`/`.*` and `⊘`/`./`
  (elementwise), `/` (scalar divisor). Shape concatenation is a deferred
  constraint, defaulted at generalisation (unknown-rank left operand is a
  scalar for `*`, a vector for `·`). `×` now means cross product.
- `==`/`/=` are the one overloaded primitive, over tensors and `Bool`, via an
  instance constraint on the same solver; comparing functions is a static
  error. `within`/`sigma` are the prefix names of `±`/`±σ`.
- Property tests over random surface programs: inference ⇒ lint with equal
  types, printed Core re-parses alpha-equivalent, hashes ignore hints and
  survive printing, linted terms never hit an internal error, inference is
  deterministic. They found and fixed two things: a binder hint shadowing a
  free name printed ambiguously (binders are now freshened), and `-3`
  desugaring differently from a negative literal (negation of a constant is
  now the negative constant). **Hash-affecting**: definitions containing a
  negated constant change hash.
- Dimensions in the type system: `Tensor s δ` with a `Dim` kind, Kennedy's
  unification, dimension-polymorphic primitives (`sqrt : Num [d^2] -> Num d`,
  `\r -> r^2 : Num d -> Num [d^2]`), the seven SI base units as primitives,
  runtime dimension vectors and printing in base units (`9.81 m s^-2`).
  Static errors name the residual: "dimensions differ by [m s^-1]". Lint's
  instance matching uses a one-shot substitution, fixing a namespace clash
  between a scheme's ids and inference's. Display units and the prelude are
  next.
- Prelude: derived SI units, the 24 prefixes on every prefixable unit,
  accepted units (min h day year L t g AU), exact SI-2019 and IAU nominal
  constants, the Levi-Civita tensor, generated from `Eval.Prelude` and entered
  into every session as one binding group (about 700 definitions, ~30 ms).
- Wedge product `∧`/`/\` (`wedge`) and 3D Hodge star `⋆` (`star`) as
  primitives; `cross` is now a prelude definition `star (wedge a b)` and `×`
  resolves through that name. `∧` therefore no longer spells boolean and,
  which is `&&` only. Units print in the customary order `kg m s …`.
- Display units: `unit name = e` declares a definition as a display unit
  (codebase metadata beside names, carried through `:update`); values carry
  a display unit through products, quotients, powers and sums (left operand
  wins) and print in it: `5 km / h` is `5 km h^-1`, `3 h + 30 min` is `3.5 h`,
  `1 AU / c to min` converts. The prelude declares its units with `unit`; `Bq`
  and `Sv` are defined through `Hz` and `Gy` so identical definitions do not
  merge their names.
- Affine arithmetic (design §3.2): tensor elements are now magnitudes, exact
  rationals or affine forms `mid + Σ cᵢ·eᵢ ± slack` whose nudges have a kind
  (bound or 1σ) and a content-addressed identity, so `x - x`, `sin 1 - sin 1`
  and `y / y` are exactly `0`, `0` and `1`. All elementary functions (`sqrt
  exp log sin cos tan asin acos atan atan2 sinh cosh tanh pi`) with rigorous
  error bounds from rational series; `norm`, `det` and `inverse`; `±`, `±σ`,
  `noise n`, `gauss n` with definition-site identity; comparisons and integer
  rounding fail with "cannot decide" instead of guessing (`:set sigma k`);
  certain-digit printing (`sin 1` is `0.84147098480789650665…`, `pi` is `3.1415926535897932384…`, `5 ± 0.1`,
  `G` is `6.67430e-11 ±σ 1.5e-15 m^3 kg^-1 s^-2`), `:exact`, `:budget`,
  `:set precision n`. Precision means significant digits (not bc's decimal
  places); working precision is `precision + 4`, so Planck-scale quantities
  keep their digits. Prelude: `G` with its CODATA σ, `M_earth` and `M_sun` derived from
  the nominal `GM` values, `deg`, `arcmin`, `arcsec`.
- Type-directed program generator for the property tests (`test/Gen.hs`):
  every program is built from a chosen closed type (numbers, tensors to rank
  three, dimensions, Bool, functions), so none is discarded; it covers
  polymorphic lets used at two types, products, contractions, wedge, star,
  sections, composition and units, and pins operands whose rank inference
  could not see so that defaulting never changes the intended type. A new
  property checks the generator itself (the intended type is an instance of
  the inferred scheme); the six pipeline properties run over both
  generators. Building and running it found, and this fixes, five bugs in
  `lib/`: a let inside an
  operand of `*`, `@` or `==` defaulted that operator's constraint
  (`[1, 2] * (let y = 1 in [3])` was rejected); a let generalised variables a
  pending product constraint tied to the enclosing scope
  (`\k -> let g = \v -> k * v in g [1, 2]` was typed `Num d -> Tensor s d`,
  and lint then rejected its uses); generalisation flipped an inverted
  dimension variable in the scheme but not in the elaborated term (lint
  rejected the let; now done through the substitution, and over all of a
  cycle's members at once, since they share quantified variables); sections and composition printed the desugarer's binder
  names (`\§s0 -> …`), which do not re-parse; and `neg 3` printed as `-3`,
  a different term. Also fixed: a dimension equation with no integer
  solution, `sqrt (1 m)`, looped in Kennedy's Euclid step instead of failing.
  No hashes change; some definitions' stored types do (the second bug's were
  unsound).
- Tensor literals take `;` for rows and `;;` for planes: `[1, 2; 3, 4]` is
  `[[1, 2], [3, 4]]`, `[1; 2]` is a 2×1 matrix. Elements stay comma
  separated. Two literals side by side (`5 4 3`, `2 [1, 2]`) are now a parse
  error asking for the multiplication; the quantity rule is for `5 m/s`.

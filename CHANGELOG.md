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
- Measurement identity (design §3.2.4). Every `±`, `±σ`, `noise` and `gauss`
  now carries a label in Core: the desugarer stamps the name of the enclosing
  definition, so `let a = 5 ± 0.1` and `let b = 5 ± 0.1` are different terms
  and independent measurements (`a - b` is `0.0 ± 0.2`, `a - a` is `0`); the
  stamp is not printed and the text round-trips. A written `#label` names the
  unknown itself, shared across definitions and midpoints: `5.0 ± 0.1 #s7`
  and `5.2 ± 0.1 #s7` differ by exactly `0.2`. Labels show as the source in
  `:budget`. **Hash-affecting**: every definition containing declared
  uncertainty changes hash (its name is now part of it), and the encoding of
  `Noise` and `Uncertain` gains a label field.
- Tensors print with the same separators they are written with: `5 * a` is
  `[5, 10, 15; 20, 25, 30; 35, 40, 45]`, rank three uses `;;`. A tensor whose
  outermost axis has length one stays nested so that it reads back at the
  same rank.
- Juxtaposition is for units only: `5 g`, `5 km/h`, `3 (m/s)` and `90 deg`
  work as before, but `5 a` for a matrix `a`, `2 pi` and `3 f x` are now
  errors that ask for the `*`. The parser builds a `Scale` node and the
  desugarer, which knows which names were declared units, checks it.
- Persistence (design §7.4). A codebase is a directory: `format`, one file per
  term in the storage encoding (canonical bytes plus binder names), and an
  append-only `names.log` of bind, unname and unit events that is replayed
  on load; types are recomputed. `eval` uses `--codebase DIR`, else a `.eval`
  directory above the working directory, else `$XDG_DATA_HOME/eval`;
  `--no-codebase` runs in memory. The prelude is entered first, in memory,
  and the log on top, so user rebindings of prelude names persist and prelude
  changes show up as stale dependents. Every successful input is written
  through. Decoder for the canonical encoding (`decodeStored`), a
  property-tested round trip. The REPL uses haskeline with a history file in
  the store, and `:store` shows which store is in use. core.md records the
  hash-stability policy: desugaring changes need no migration, encoding and
  Core changes bump the format number.
- Plane angle is a dimension (design §3.2.11). `rad` is the eighth base unit;
  `sin`, `cos` and `tan` take `Num [rad]`, `asin`, `acos`, `atan` and `atan2`
  return it, `sr = rad^2`, `lm = cd sr`, and `rad` takes prefixes. `sin 1` is
  a type error that asks for `1 rad` or `45 deg`; `rad/s` and `Hz` are now
  different types; arc length is `r * θ / rad`. Stored definitions that
  applied the circular functions to plain numbers no longer typecheck and are
  reported as notes at load. Hash-affecting for `sr`, `lm` and `lx`.
- Display units of one dimension cancel: `2 m * 90 deg / rad` prints
  `3.14… m`, `3 h / min` prints `180`, `(2 km)^2 / m` prints `4000 km`. Hints
  now carry each unit's own dimension and factor.
- Points and scales (design §3.6). Affine quantities get their own type:
  `Point d` with `p .- q : Num d` and `p .+ v : Point d`, written on a
  `scale name = step at origin` and printed on the scale they were written
  on. `20 °C .+ 5 K` is `25 degC`, `77 °F .- 68 °F` is `9 deltaF`,
  `20 degC + 5 degC` is a type error that says why. Points compare with `==`
  and `<`; the comparisons are now instance-constrained over numbers and
  points. Prelude: `degC`, `degF`, `degR`, `kelvin` with step units `deltaC`
  and `deltaF`; epochs `JD`, `MJD`, `J2000`, `unix`; `gauge` pressure. The
  type language gains `Point` and `Scale`; Core is unchanged.
- Sums take the smaller unit, so `5 km + 3 m` and `3 m + 5 km` both print
  `5003 m` (was: the left operand's). Design §3.2.12 states the display rule
  in order: `to` wins; else the written units, simplified; else base units.
  Products are never renamed to a named unit.
- Units and scales are names, not references (design §3.2.12). Every `Ref`
  in Core carries the name the author wrote as a hint, ignored by the hash
  like binder hints and kept in the store, and the evaluator asks whether
  that name was declared a unit. `unit dozen = 12` and `let eggs = 12`
  share a hash yet `3 dozen` and `eggs + 1` print `3 dozen` and `13`; `Bq`
  and `Hz` are both `1/s` again; a `let` that rebinds a unit name makes it a
  quantity; `:alias` of a unit is a unit; a renamed unit prints under its new
  name. Storage format 2; format-1 stores migrate in place on first open.
  Hashes are unchanged.
- Points over tensors (design §3.6). `Point` and `Scale` take a shape:
  `scale site = m at [100, 200, 0] m` is a frame, `[1, 2, 3] site` a
  `Point (Vec 3 [m])`, `p .- q` a displacement, `p .+ v` a moved position,
  `p.0` a coordinate as a scalar point, `p to eci` the same position in
  another frame. Scalar points print as `Point [K]` as before.
- `:prefer unit` and `:unprefer unit` (design §3.2.12): a display unit per
  exact dimension, applied after `to` and before the written units, one per
  dimension, kept in the codebase so it persists. `:prefer` alone lists them.
- Covariance (design §3.4, §3.5). `±` and `±σ` work on tensors with one
  independent nudge per component (a scalar uncertainty or one of the
  value's shape); `v ±σ P` with a covariance matrix is a vector with that
  covariance, stamped like every `±`. `covariance v` gives Σ cᵢcᵢᵀ over the
  statistical nudges exactly, `cholesky` its square-root factor, and
  `:covariance e` prints the covariance (or variance) with the bound box
  beside it. The design's `withCovariance` became `±σ` with a matrix.
- Tuples, lists and `case` (design §2.3, §5.1). `(a, b)` and `{a, b, c}` are
  data; `case e of` takes them apart one constructor deep, with `_` or a
  variable standing for the constructors not written, and `if` is a case on
  `Bool`. Core gains `Con` and `Case` and loses `If` and the boolean literal
  (core.md §5): storage format 3, and the first hash-changing migration, which
  re-hashes every stored term that used them and rewrites references and the
  log. Prelude: `fst`, `snd`, `map`, `filter`, `foldr`, `foldl`, `length`,
  `reverse`, `zip`, `range`. `==` works on tuples and lists of comparable
  things. A closing bracket now ends layout blocks opened inside it.
- User data types (design §2.3). `data Shape = Circle (Num [m]) | Rect (Num
  [m]) (Num [m])` declares a sum of products with parameters of any kind,
  inferred from use (`data State n = State (Vec n [m]) (Vec n [m/s])`,
  `data Reading d = Reading (Num d) (Point [K])`), recursive through the type
  itself. Constructors are functions and `case` patterns; `:type`, `:view`
  and `:edit` know the types; types and constructor names are labels, stored
  as `types/<hash>` files and `type`/`con` log lines, and a type's identity
  is its definition stamped with its name, or structural with `structural
  data`. In Core a constructor is `UserCon hash i`; built-in constructors
  encode as before, so no format bump. Constructors and definitions share
  one namespace, the newer label winning. Not yet: `==`
  on declared types, records, mutually recursive types.
- Records (design §2.3). `data Body = Body {mass :: Num [kg], pos :: Vec 3
  [m]}` names the fields of a one-constructor type; `b.mass` reads one,
  `Body {mass = 5 kg, pos = …}` builds the record and `b {pos = …}`
  rebuilds it, all as `case` on the constructor, so Core and hashes are
  unchanged. Field names are labels (`field` log lines, `:unname .mass`),
  looked up by the field alone. A dot glued on both sides is now a field
  access; composition is `f . g` or `∘`. Printed data values parenthesise
  every compound field: `Rect (1 m) (2 m)`.
- `Rect 3 m 4 m` is four arguments again, not two quantities; a type error
  that lands on such a literal or unit now carries a hint to write `(3 m)`.
  Provenance carries hints beside spans.
- `eval [--codebase DIR] --merge OTHER` merges another store into this one
  (design §7.4): terms and types DIR lacks are copied after a hash check,
  OTHER's new log lines are added and the log is stably sorted by time, so
  the last writer per name wins. OTHER is only read (an older format is
  migrated in place and reported), merging again adds nothing, and the
  `history` file is left alone. `Eval.Store.mergeStores` and `mergeStore`
  expose it as a library function returning a `MergeReport`.

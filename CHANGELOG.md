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
- `:ls [glob] [--all | --units | --scales | --types] [: type]` browses the
  codebase: every name with its type, declared types with their
  constructors, the prelude hidden unless asked for. The type query is a
  written type whose lowercase unknown names are variables, matched by
  unification both ways, so `:ls : {a} -> Num` finds `length` and
  `:ls : Vec 3 d -> Vec 3 d -> Vec 3 [d^2]` finds `cross`.
- `eval [--codebase DIR] --merge OTHER` merges another store into this one
  (design §7.4): terms and types DIR lacks are copied after a hash check,
  OTHER's new log lines are added and the log is stably sorted by time, so
  the last writer per name wins. OTHER is only read (an older format is
  migrated in place and reported), merging again adds nothing, and the
  `history` file is left alone. `Eval.Store.mergeStores` and `mergeStore`
  expose it as a library function returning a `MergeReport`.
- `==` and `/=` on declared types (design §2.3, §4.2), derived structurally
  as for tuples and lists: a type has equality when every field of every
  constructor, at the type's arguments, has it. `Circle (1 m) == Circle (1
  m)` is true, values of different constructors are unequal, and `Just 1 ==
  Just 1` works. A recursive occurrence counts as the instance being
  derived, and which parameters need equality is a fixed point over the
  fields, so nested types (`data N a = Z a | S (N (a, a))`) are decided
  too. A type with a function field still has none.
- `mid`, `bound` and `sd` (design §3.2.9): three primitives, elementwise
  on tensors (`Tensor s d -> Tensor s d`), that take an enclosure apart the
  way the printer collapses it, keeping the operand's dimension and display
  unit: the midpoint, the bound radius `Σ_bound |cᵢ| + slack`, and the
  standard deviation `√(Σ_stat cᵢ²)`. `mid` and `bound` are exact; `sd`
  is exact when the variance is a square and otherwise an enclosure of the
  root. `bound (10 mm ± 0.1 mm)` is `0.1 mm`, and a comparison policy of
  one's own is a definition.
- Record values print with their field names (design §2.3): `Body {mass = 6
  kg, pos = [1, 2, 3] km, vel = [0, 0, 0] m s^-1}`, nesting, and reading
  back as the same value. The value printer takes a `Printer` (names for
  references and a field namer); the driver fills it from the codebase, and
  `plainPrinter` knows no field names. A constructor with an unnamed field
  still prints positionally.
- `:set unicode on|off` (design §7.3, §2.8), listed by `:set`, off by
  default. When on, output uses superscript exponents (`9.81 m s⁻²`, `Num
  [m s⁻²]`, `x²` in `:view`), `→` for `->`, `λ` for `\`, and `≤ ≥ ≠ ∨` for
  `<= >= /= ||`; `*` stays `*`, since `×` is the cross product. Every form
  lexes to the same tokens as its ASCII one. A `Spelling` (`Ascii` or
  `Unicode`) reaches the unit, type and term printers through `renderUnitsIn`,
  `renderTypeIn`, `renderTermIn` and the value `Printer`; the default
  rendering is unchanged.
- A constructor's braces are record syntax only when `{name ::` follows, so
  `data H = G {Num}` declares a constructor with one list-typed field.
- `contract i j t` and `permute [p0, …, pk-1] t` at any rank, with literal
  index positions (design §3.3, §4.2). `contract` sums the diagonal of two
  positions of equal length and drops both (`contract 0 1` of a square
  matrix is its trace; `a · b` is `contract (r-1) r (a * b)`); `permute`
  puts position `p_q` of `t` at position `q` and leaves later positions
  alone (`permute [1, 0]` is `transpose`). Both keep the dimension and the
  display unit and are linear in the nudges. The scheme is computed from the
  literals, like `Pow`'s dimension from its exponent: `\t -> contract 0 2 t`
  is `Tensor (n : m : n : s) d -> Tensor (m : s) d`. The positions are `Lit`
  arguments of the `PrimApp` (arities 3 and 2), so Core, the encoding and
  stored hashes are unchanged; the desugarer rejects non-literal, negative,
  fractional or repeated positions and a non-permutation, inference reports a
  too-small known rank ("contract 0 2 needs a tensor of rank at least 3, got
  Mat 2 2") and unequal paired lengths ("lengths differ: 2 and 3"), and lint
  rebuilds the scheme from the `TLit` arguments. The prelude's `trace a =
  contract 0 1 a` is `Mat n n d -> Num d` at rank two and the partial trace
  over the first two positions above it.
- Slicing along any axis: `m._.0` is column 0 of a matrix and `t._._.2`
  position 2 of the third axis (design §2.10, §3.3, §4.1). Each glued `._`
  (a new `TWild` token, under the same adjacency rule as `.0`) skips one
  axis and a position must follow (`m._` alone is a parse error); the chain
  reads left to right, so `t._.0.1` is `(slice 1 0 t).1`. The surface node
  `Slice e k i` desugars to the new primitive `slice k i t` (arity 3, axis
  and position as `Lit` arguments, like `contract`), which may also be
  written out with the same literal checks; `Proj` is unchanged and `slice 0
  i t` stays a different term from `t.i`. `slice k i` is typed from its
  literals as `Tensor (l0 : … : lk-1 : n + i + 1 : s) d -> Tensor (l0 : … :
  lk-1 : s) d`, so `\m -> m._.0` is `Tensor (n : m + 1 : s) d -> Tensor (n
  : s) d`; a known axis too short is "position 2 is out of range for axis 1
  of length 2" and a known rank too small "slice 1 0 needs a tensor of rank
  at least 2, got Vec 3". The kernel is a strided gather that keeps the
  dimension, the display unit and every nudge, and `:view` prints `slice k i
  t` with `k ≥ 1` back as `t._.i`. Core, the encoding and stored hashes are
  unchanged; the property generator now builds slices too.
- `indices`, `vzipWith` and the prelude's `vimap` (design §3.3).
  `indices : Vec n d -> Vec n` is `[0, 1, …, n-1]`, exact and dimensionless,
  as long as its argument, whose components it does not force; a matrix
  argument is a type error. `vzipWith : (Num d -> Num d1 -> Num d2) ->
  Tensor s d -> Tensor s d1 -> Tensor s d2` is `⊙`'s general form: it
  applies a two-argument function to each pair of components of two tensors
  of one shape ("lengths differ: 2 and 3" otherwise), with `vmap`'s
  strictness and no display unit. `vimap f v = vzipWith f (indices v) v` is
  `(Num -> Num d -> Num d1) -> Vec n d -> Vec n d1`, a map that sees each
  component's position. The position is a value, never a literal, so there
  is no computed indexing (design §2.10): `x ^ i` is still a parse error and
  `v.i` reads a record field `i` ("unknown field `i`"). Two primitives appended (arities 1 and 3); Core, the
  encoding and stored hashes are unchanged.
- `timap`, the indexed map at any rank, and `rank`, the first type-level
  function (design §3.3, §4.1, §4.2). `timap : (Vec (rank s) -> Num d ->
  Num d1) -> Tensor s d -> Tensor s d1` applies a function to each
  component's multi-index, a vector of exact dimensionless naturals as long
  as the rank, and then to the component, with `vmap`'s strictness and no
  display unit: `timap (\i x -> if i.0 == i.1 then x else 0) m` keeps a
  matrix's diagonal. A length may now be `rank s + k`, normalised on every
  substitution so that it only names an unbound shape variable. Against a
  literal it fixes the shape to that many fresh lengths; against `n + m` it
  binds `n`, or gives the shape leading lengths when the rank must be at
  least `m`; so `let diag t = timap (\i x -> if i.0 == i.1 then x else 0) t`
  generalises to `Tensor (n : m : s) -> Tensor (n : m : s)` and `diag [1, 2,
  3]` is refused ("expected Tensor (n : m : s), got Vec 3: a tensor of rank
  at least 2 against a vector"). Two ranks of different unknown shapes wait
  as a pending rank equation, which is an error if still unsolved at
  generalisation. Lint compares the normalised instance with `timap`'s
  scheme, and accepts projections from `Vec (rank s + k)` below `k`. The
  prelude's `vimap` is unchanged. One primitive appended (arity 2); the type
  encoding gains length tag 2 for `rank s + k`, appended, so Core, stored
  terms and hashes are unchanged.
- `it`, the last result, and the unicode echo (design §7.3, §7.5). After an
  expression statement evaluates, `it` names that expression for later
  expressions and for `:type`, `:view` (`it = 1 + 2`), `:exact`, `:budget`,
  `:covariance`, `:core`, `:hash` and `:lint`; each expression on a line is
  `it` for the next, and an input that fails leaves the previous one. It is
  bound in a codebase built for each expression on top of the staging one,
  which keeps the terms `it` was checked against, so it survives a replaced
  or forgotten pending definition. It is never stored: `:ls` does not list it, `:add` and
  `:update` do not see it, and a definition that mentions it is refused
  ("`it` is the last result and cannot be stored; paste its definition (:view
  it) instead"), as is a definition named `it`. With `:set unicode on`, a
  statement line is first echoed in its unicode spelling on a note line
  starting `  ≡ `: `2 +-s 0.1 * 3 km/h` as `2 ±σ 0.1 * 3 km/h`, `\x -> x^2
  <= 4` as `λx → x² ≤ 4`. `Pretty.respell` re-spells the lexed tokens at
  their spans and keeps every other character; names, `*`, `/` and `&&`
  keep their spelling, a caret power becomes a superscript only when glued
  to an atom with an integer literal exponent, and the result must lex to the
  same tokens. A line with nothing to re-spell, a command, a failed line and
  a loaded file are not echoed; with unicode off nothing changes.
- Design §3.3, §4.3, §4.6 and §4.7 no longer say that `det` needs a
  statically known size or is typed `Mat n n d -> Num [d^n]`: it is the
  plain primitive `Mat n n 1 -> Num 1`, polymorphic in the size and on
  dimensionless matrices only, and a matrix with a unit is a dimension
  error. Behaviour unchanged.
- REPL editing aids (design §7.3, §2.8). TAB completes `:` commands at the
  start of a line, the arguments of `:set` and `:colour`, file names
  after `:load`, record fields after a glued `.` (`b.ma` gives `b.mass`),
  and otherwise the session's names, types, constructors and keywords.
  `\name` then TAB
  enters a character, as in Julia: `\mu` gives `μ`, `\pm` gives `±`,
  `\pms` gives `±σ`, `\^2` gives `²`. The table is in the new module
  `Eval.Unicode`, and a test checks each entry against the lexer. Output
  is coloured when stdout is a terminal, `TERM` is not `dumb` and
  `NO_COLOR` is not set. Errors are red with bold red carets. Notes, the
  types in `:ls` lines and the trailing units of values are dim. The prompt
  is bold. The REPL-level command `:colour on|off` overrides the default.
  The logic is pure, in the new module `Eval.Repl`. The text that `feed`
  prints is unchanged.
- Multi-line input in the REPL (design §7.3). An input goes on at the
  continuation prompt `… ` while a bracket is open, while its last token
  cannot end an input (`=`, `->`, `\`, `|`, `,`, `;`, an infix operator,
  `±`, or a keyword such as `of`, `in`, `then`, `else`), or after a line
  that ends in `of` or `where`, whose block runs to a blank line. A blank
  line ends the input as it stands; Ctrl-C or Ctrl-D at the continuation
  prompt abandons it. The decision reads the lexer's tokens, so comments
  never count, and a `:` command never goes on. `eval -i` does the same and
  echoes each line after its prompt. Each physical line is its own history
  entry. The pure part is `Eval.Repl.needsMore`; one-line inputs and what
  `feed` prints are unchanged.
- REPL colour is now a syntax-highlighting theme on the 16 ANSI colours
  (design §7.3). It has no dim text, because some terminal themes do not
  show it. Keywords are magenta. Units, base units and scales are cyan.
  Types, constructors and the built-in heads are yellow. Notes, comments,
  `#hash` references and the `≡` mark are bright black. Errors are red,
  carets bold red, and the prompt bold. Numbers, operators and other
  names are plain. Each line is lexed and coloured token by token: the `≡`
  echo, `:view`/`:edit` output, `data` declarations, values, `:type`
  output, the type in `:ls` lines, an error's source excerpt (the carets
  stay aligned) and the input echo of `eval -i`. A line that does not lex
  is coloured by its kind, as before. New in `Eval.Repl`: `Names`,
  `namesOf`, `highlight`, `highlightType`, `render` and `echoInput`.
  `paint` now takes the `Names`. Without colour every byte is as before.
- Namespaces (design §7.6). A name is a dotted path, `orbital.period`; a
  namespace is only a prefix on labels, so terms, hashes, the store and its
  log are unchanged. `namespace a.b` opens an indented block of statements
  (`let`, `unit`, `scale`, `data`, nested `namespace`, `use`) whose labels
  get the path; `use a.b` and `use a.b as k` make its names resolve bare or
  under `k.`. A free name resolves to a local binder, then the current
  namespace, then the `use`d namespaces (two offering it is an error), then
  the root; `.name` is absolute. A dot chain on a free name is a qualified
  name when its longest prefix names a definition or constructor, else
  field access. A name is never both a label and a namespace. The
  namespace reaches a hash only through the owner stamps of `±`
  definitions and nominal types, which are the full path (see below).
  Names print as Unison prints them, the shortest spelling
  that resolves back. New commands `:namespace [path|.]`, `:uses`,
  `:unuse`, `:rename old new` and `:move name… namespace`; `:alias`,
  `:unname` and `:ls` take a namespace. `:load` keeps a file's `use`s to
  the file. New tokens: the keywords `namespace` and `use` (`as` stays a
  name: it is attoseconds), and `TAbs` for a dot not glued to a value.
- `:export [namespace] [file]` (design §7.4): the stored codebase, or one
  namespace, as source that `:load` reads back to the same labels and
  hashes. Namespaces become nested `namespace` blocks with root definitions
  outside them; definitions print as `:edit` prints them, spelled for their
  block (`.km` where the block shadows a root `km`); the standard library
  under `std` is left out unless asked for (see below); types come first, then terms after what they reference, a
  cycle's members together. A definition on a version no name points at
  refuses the export. Without a file the source is printed; the pending
  scratch is not exported, and a comment or note says so. New in
  `Eval.Driver`: `exportSource` and `exportRequest`.
- The standard library lives in the codebase under `std` (design §7.7).
  The prelude is no longer entered in memory under every session: a new
  store is created and seeded with the library as one group under `std`
  (`std.km`, `std.G`, `std.map`, …) and a stored `use std`, its log lines
  stamped with time 0 so they sort before the user's and are the same in
  every store (a merge of two seeded stores brings nothing across for the
  library); an existing store is loaded on top of the empty codebase;
  `--no-codebase` seeds in memory. The codebase keeps a list of stored
  uses (`Codebase.uses`, log lines `use path [as alias]` and `unuse …`),
  which resolve after the root, so a root `c` shadows `std.c`. `:uses`
  marks them `(stored)`; `:use path [as alias]` adds one; `:unuse` removes
  a stored one when one matches, else the session's. `:ls` alone lists the
  current namespace's own labels and one line per namespace under it
  (`namespace std (794 names)`), with no hidden-prelude footer; `--all`
  lists full paths; a glob matches the full path or its last segment.
  `:export` leaves `std` out unless asked (`:export std`), heads the text
  with the stored uses as `use` statements and spells names for them, and
  refuses a bare word that is no namespace instead of writing a file of
  that name (a file needs a `/` or a `.`). `:stdlib upgrade`, a sketch:
  adds new library names, updates names still on their seeded binding
  (with propagation), keeps the user's. New: `Eval.Prelude.stdlibSource`,
  `stdlibNames` (full paths, replacing `preludeNames`), `stdlibCodebase`,
  `stdlibMoved`; `Eval.Driver.seededSession` (replacing `preludeSession`)
  and `stdlibUpgrade`; `Eval.Store.Seed`, `stdlibSeed`, `seedStore`;
  `openStore` and `mergeStores` take the seed; `qualifyWith` takes the
  stored uses.
- Store format 4. `formatVersion` is no longer `storageVersion` (still 3):
  format 4 changes what a store holds, not how a term is encoded. A
  format-3 store is migrated on open (formats 1 and 2 chain through 3) by
  seeding it before its own log, so the user's root bindings still shadow
  the library and the terms they reference are still on disk; no stored
  hash moves.
- Hash change: the owner stamp of a `±`, `noise` or `gauss` and of a
  nominal type is the definition's full path (`lab.offset`, `std.G`,
  `orbital.Body`), not its last segment, so `lab.offset = 1 ± 0.1` and
  `field.offset = 1 ± 0.1` are two measurements and `a.Body` and `b.Body`
  two types. The library's `std.G`, `std.M_earth` and `std.M_sun` therefore
  have new hashes; every other library definition keeps the hash the root
  prelude gave it. The format 3 to 4 migration records an old `G` that a
  user term still uses as the history of `std.G`, so `:todo` reports the
  term and `:upgrade std.G` moves it. `:rename` and `:move` of a stamped
  definition or type re-stamp and re-hash it and propagate to everything
  that uses it, reporting `re-hashed` and `upgraded` lines (new in
  `Eval.Update`: `restamp`).
- `:edit` is an editor round trip (design §7.3, §10 item 10). `:edit` (the
  codebase but `std`), `:edit namespace` (`:edit std` the library) and
  `:edit name` (one definition or type, with its cycle) write the scope to
  a temporary `eval-edit-….ev` in the `:export` format under a header that
  says what saving does, open `$VISUAL` or else `$EDITOR`, and reconcile the
  saved file with the codebase, all or nothing: what is new is `added`, a
  label on another reference `updated` (or `upgraded` when only what it uses
  moved), a label of the scope the file no longer defines `removed` as
  `:unname` does (not for one name), and dependents outside the file are
  propagated as `:update` does, constructor users of a replaced type
  included; `nothing changed` when nothing did. A parse or type error, an
  expression, a file that no longer defines the one name, or one that would
  remove every label of the scope is refused, and the file is kept for
  `:edit --file path [scope]`, which reconciles a file without an editor.
  Scripted (`-i`), one-shot, or with no editor set, `:edit` prints what it
  would have opened, the pasteable statement for one name as before, with a
  note saying why. TAB completes a file name after `:edit --file`. New:
  `Eval.Driver.EditScope`, `EditRequest`, `editRequest`, `applyEdit`,
  `editScopeArgs`, `editorNote`; `Eval.Update.propagateWith` (a constructor
  map besides the reference map), `ConMap`, `conTypes`, and `restampTerm`
  exported. The executable depends on `process`.
- A `let` that takes over a unit or scale name now stays a plain quantity
  after a restart: the store logs `unflag name` when a bound name loses its
  flag. Before, the flag came back on reload.
- `rank s` can be written as a length in a `data` declaration: `data Idx s =
  Idx (Vec (rank s))` has `Idx : Vec (rank s) -> Idx s`. `rank` cannot name a
  parameter.

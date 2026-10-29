# Design: `eval`

A small, pure, unit-aware, content-addressed calculator language.

This document is the design reference for the project. It fixes the syntax, the
value model, the type system, the nominal form that gets hashed, the codebase
model, and the roadmap. Code should follow it; where code and this document
disagree, update one or the other deliberately.

## Contents

1. Goals and non-goals
2. Surface syntax
3. Values, numbers and units
4. Type system
5. Core and Typed Core
6. Hashing
7. Codebase and names
8. Evaluation
9. Module layout and libraries
10. Roadmap
11. Open questions
12. Worked scenario: iapetus

---

## 1. Goals and non-goals

Two concrete uses drive every priority in this document.

**A quick CLI calculator that understands units.** Something to type
`eval '5 km/h to m/s'` into every day. It must give exact answers, handle units
without ceremony, and start instantly.

**A function library for the iapetus project.** Orbital-mechanics functions that
carry units, work on vectors and matrices, and track how approximation error and
input uncertainty build up through user-defined functions. The library needs stable
versioning of definitions over years.

### Goals

- Exact arithmetic by default: `1/3 * 3` is `1`, not `0.9999…`.
- Units of measure checked statically. `1 m + 1 s` is a type error, not a runtime
  surprise.
- Pure expressions and immutable bindings, with Haskell-like semantics.
- Rigorous tracking of approximation error and declared uncertainty through
  arbitrary user code, with an error budget per source.
- Vectors and matrices as first-class dimensioned values.
- Every definition has a nominal form with a content hash. Names are labels that
  point at hashes. Versioning is label management, as in Unison.
- Interactive use (REPL) and one-shot use (`eval 'expr'`) from day one.

### Non-goals for v1

- Strings, lists, user-defined data types, general type classes, IO, effects.
- Temperature scales with offsets (°C, °F). They are affine, not multiplicative,
  and need a different unit model.
- Vectors or matrices whose components have different dimensions (see §3.3).
- Performance beyond "interactive for a few thousand steps".
- Non-SI unit systems beyond a handful of accepted units iapetus needs.

### Architecture: three representations

The implementation is organised around three representations of a program, in the
spirit of GHC's source / Core / STG split. Each has one job.

```
  source text
      │  lex (unicode → canonical tokens), parse
      ▼
  Surface AST          rich: unicode, sugar, sections, where, superscripts, spans
      │  desugar, resolve names → refs
      ▼
  Core                 small, named-with-hints, untyped; this is what gets hashed
      │  infer, elaborate (overloads → dictionaries, explicit type abstraction)
      ▼
  Typed Core           System-F-like; what the interpreter and compiler consume
      │
      ├─▶ interpreter (v1)
      └─▶ compiler (later)
```

- **Surface AST** (§2) is a faithful tree of what the user typed, with source spans
  for error messages. Everything convenient lives here and nowhere else.
- **Core** (§5) is the desugared language: about a dozen constructors, one-parameter
  lambdas, resolved references, no operators, no sugar. Binders keep a *name hint*
  that hashing and equality ignore. The content hash (§6) is computed from Core,
  so a definition's identity is independent of its types and of how overloading
  was resolved. This is Unison's choice and it keeps hashes stable when the type
  system grows.
- **Typed Core** (§5.3) is Core after inference and elaboration: every binder is
  annotated, type, dimension and length abstraction and application are explicit,
  overloaded operators are resolved to monomorphic primitives or to dictionary
  parameters, and defaulting has happened. It is stored in the codebase as derived
  data under the Core hash and can always be recomputed. The interpreter (§8) runs
  it directly; a compiler later takes it as input.

The pretty-printer goes the other way, Core → surface text, and can emit either
unicode or ASCII spellings (`:set unicode on|off`).

---

## 2. Surface syntax

The surface language is deliberately close to Haskell, with a unicode layer and a
handful of calculator-specific sugars. Everything in this section is removed by
desugaring (§2.9); the type checker never sees it.

### 2.1 Lexical structure

- **Identifiers**: a letter or `_`, then letters, digits, `_`, `'`, and
  subscript digits (`v₀`, `e₁`). Any Unicode letter is allowed, so `Ω`, `µ`, `θ`,
  `Δv` are identifiers. Source is NFC-normalised and the compatibility
  confusables are folded (`µ` U+00B5 → `μ` U+03BC, `Ω` U+2126 → `Ω` U+03A9).
  ASCII aliases exist for every prelude unit that needs them (`ohm`, `u`).
- **Numbers**: `3`, `9.81`, `1e-3`, `6.674e-11`, `1_000_000`. A number literal is
  always an exact rational; `9.81` is exactly 981/100. `1/3` is an expression, not a
  literal. Underscores are ignored.
- **Comments**: `--` to end of line, `{- … -}` nestable blocks.
- **Keywords**: `let`, `in`, `where`, `if`, `then`, `else`, `to`, `true`, `false`.
- **Operators**: `+ - * / ^ ± == /= < <= > >= && ||` and their unicode spellings
  (§2.8). A name in backticks is an infix operator: `a `dot` b`.
- **Statement separators**: a newline at indentation zero, or `;`. A line that
  starts with whitespace continues the previous statement.

### 2.2 Statements

A *program* (a file, a piped stdin, or one multi-line REPL input) is a sequence of
statements. All statements in one input form a **binding group**: they may refer
to each other in any order, and mutual recursion is possible only within a group.
A single REPL line is a group of one.

```
let x = 2 + 3                   -- bind a name
let f x y = x * y + 1           -- sugar for: let f = \x y -> x * y + 1
f 3 4                           -- a bare expression: evaluate and print
```

A `let` without `in` at the top level *proposes* a definition: it goes into the
scratch (§7.5), where it is checked, hashed and usable by later expressions but
not stored. `:add` and `:update` move scratch definitions into the codebase (§7).
Within one input a name may be defined only once, as in a Haskell module; across
REPL inputs a pending definition is replaced by a newer one.

Layout is deliberately simpler than Haskell's: a token that starts a line at the
column of its enclosing context starts a new statement (or `where` binding), a
token further right continues the previous one, and there is no parse-error rule.
So a multi-line `let … in` expression must indent the `in`, and a bracket that
spans lines must indent its continuation lines.

### 2.3 Expressions

```
\x y -> x + y                   -- lambda, one or more parameters
let a = 1 in a + a              -- local, non-recursive binding
if x > 0 then x else -x         -- conditional, both branches same type
f a b                           -- application by juxtaposition, left-associative
(f a) b                         -- the same
```

`let … in`, `\ … ->` and `if … then … else` extend as far to the right as possible,
as in Haskell.

Further sugar, all removed by desugaring (§2.9):

```
let f x = x * k where k = 2          -- where: local bindings after a definition
(+ 1)   (2 *)   (`dot` v)            -- operator sections
a `dot` b                            -- infix application of a named function
f ∘ g                                -- composition, \x -> f (g x)
```

### 2.4 Vector and matrix literals

```
[1, 2, 3]                       -- Vec 3
[[1, 0], [0, 1]]                -- Mat 2 2
[x, y, z] m                     -- Vec 3 [m], via the quantity rule
```

A vector literal is a bracketed, comma-separated list of expressions. A matrix
literal is a bracketed list of vector literals of equal length. Components may be
any expression. Ragged rows are a parse error.

### 2.5 Operators

From tightest to loosest:

| Level | Operators | Associativity | Notes |
|---|---|---|---|
| 10 | application, quantity rule | left | `f a b`, `3 m` |
| 9 | `^` | n/a | exponent must be an integer literal, optionally negative, so `^` cannot chain; a glued superscript is the same operator |
| 8 | unary `-` | prefix | `-x` |
| 7 | `*`/`⊗` `·`/`@` `⊙`/`.*` `⊘`/`./` `/` | left | tensor product, contracting product, elementwise product and division, scalar division (§4.2) |
| 7 | `×`/`><` | none | cross product |
| 6 | `+` `-` | left | overloaded over Num, Vec, Mat |
| 5 | `±` `±σ` | none | `value ± bound`, `value ±σ stddev`, see §3.2.5 |
| 4 | `==` `/=` `<` `<=` `>` `>=` | none | ordering on Num only |
| 3 | `&&` | right | |
| 2 | `\|\|` | right | |
| 1 | `to` | none | unit conversion, lowest so `5 km / h to m/s` reads naturally |

`+ - * /` are overloaded; everything else that works on vectors or matrices is a
named function: `dot`, `cross`, `norm`, `transpose`, `inverse`, `det`, `identity`,
`vmap`, `noise`, `gauss`, `covariance`, `cholesky`. Component access is the postfix
projection `v.0`, `m.1.2` (§2.10), never a function taking a computed index.

### 2.6 The quantity rule

A number literal followed by one or more *unit atoms* denotes a product:

```
quantity ::= number unitatom+
           | vector unitatom+
unitatom ::= atom [ '^' [ '-' ] natural ]
```

A unit atom is an atom (identifier, parenthesised expression, or literal)
optionally raised to an integer power. The whole quantity binds like an
application. Examples:

| Written | Means |
|---|---|
| `3 m` | `3 * m` |
| `3 m^2 kg` | `3 * m^2 * kg` |
| `9.81 m/s^2` | `(9.81 * m) / (s^2)` |
| `5 km/h` | `(5 * km) / h` |
| `[1, 0, 0] km` | `[1, 0, 0] * km` |
| `3 (f x)` | `3 * (f x)` |
| `3 f x` | `3 * f * x` |

The last line is the cost of the rule: a literal followed by identifiers is a
product, never an application of `f` to `x`. Write `3 (f x)` if you mean the
application. The rule applies only to literals. A variable needs an explicit
operator: `x * km`.

The rule is a parse-time rewrite to `*`. Core (§5.1) never sees it.

### 2.7 Grammar

The grammar is over canonical tokens, after the unicode mapping of §2.8.

```
program    ::= statement ( sep statement )*
sep        ::= newline-at-column-0 | ';'
statement  ::= 'let' name param* '=' expr [ 'where' bindings ]
             | expr
bindings   ::= binding ( sep binding )*            -- indented block
binding    ::= name param* '=' expr
param      ::= name
expr       ::= 'let' name param* '=' expr 'in' expr
             | '\' param+ '->' expr
             | 'if' expr 'then' expr 'else' expr
             | binary
binary     ::= operator-precedence parse over 'unary' using the table in 2.5,
               with `name` as an infix operator at level 9
unary      ::= '-' unary | 'sqrt' unary | power
power      ::= app [ '^' [ '-' ] natural ]
app        ::= quantity | atom atom*
quantity   ::= number unitatom+ | vector unitatom+
unitatom   ::= atom [ '^' [ '-' ] natural ]
atom       ::= primary ( '.' projection )*          -- no whitespace around '.'
projection ::= natural
primary    ::= number | name | 'true' | 'false'
             | '(' expr ')' | section | vector | matrix
section    ::= '(' operator expr ')' | '(' expr operator ')'
vector     ::= '[' expr ( ',' expr )* ']'
matrix     ::= '[' vector ( ',' vector )* ']'
```

### 2.8 Unicode spellings

The lexer maps unicode to canonical tokens. Every construct has an ASCII spelling,
so a plain keyboard is never a barrier, and the pretty-printer can emit either.

| Unicode | ASCII | Meaning |
|---|---|---|
| `λ` | `\` | lambda |
| `→` | `->` | arrow |
| `⊗` | `*` | tensor (outer) product, which includes scalar scaling and plain multiplication; name `outer` |
| `·` `⋅` | `@` | contracting product: dot, matrix-vector, matrix-matrix; name `dot` |
| `×` | `><` | cross product; name `cross` |
| `⊙` | `.*` | elementwise product; name `emul` |
| `⊘` | `./` | elementwise division; name `ediv` |
| `÷` | `/` | division by a scalar; name `div` |
| `≤` `≥` `≠` | `<=` `>=` `/=` | comparison |
| `∨` `¬` | `\|\|` `not` | boolean or, not; boolean and is `&&` only, because `∧` is the wedge product |
| `∧` | `/\` | wedge (exterior) product; name `wedge` |
| `⋆` | `star` | 3D Hodge star, prefix; name `star` |
| `±` | `+-` | declared hard bound |
| `±σ` | `+-s` | declared standard uncertainty (1σ) |
| `√` | `sqrt` | prefix: `√x`, `√(a² + b²)` |
| `∘` | `.` | composition |
| `²` `³` `⁻¹` … | `^2` `^3` `^-1` | superscript digits and `⁻` as a power: `m/s²`, `s⁻²` |
| `π` | `pi` | the constant |
| `°` | `deg` | postfix unit: `45°` is `45 deg` |
| `″` `′` | `arcsec` `arcmin` | postfix units |
| `₀` `₁` … | `_0` `_1` … | subscripts inside identifiers only |

Rules: superscripts bind as `^` does, so `3 m²` is `3 * m^2` by the quantity rule.
A superscript is only a power when it follows an atom without a space; `x ²` is an
error. `°` and the arc marks attach to the preceding number without a space and
are unit atoms, so `45° + 30′` works.

### 2.9 Sugar and desugaring

Everything in this table is removed before Core. The right column is Core written
in surface notation.

| Surface | Core |
|---|---|
| `let f x y = e` | `let f = \x -> \y -> e` |
| `\x y -> e` | `\x -> \y -> e` |
| `let f x = e where k = …` | `let f = \x -> let k = … in e` (where-bindings are non-recursive and scope over `e`) |
| `a `g` b` | `g a b` |
| `(+ 1)`, `(2 *)` | `\x -> x + 1`, `\x -> 2 * x` |
| `vmap sqrt v`, `foldr add 0 xs` | `vmap (\x -> sqrt x) v`, … : a primitive used as a value is eta-expanded to its arity, because Core primitives are saturated (§5.1). The pretty-printer eta-reduces these for display |
| `f ∘ g` | `\x -> f (g x)` |
| `3 m²`, `3 m s⁻²` | `3 * m^2`, `3 * m * s^-2` (quantity rule) |
| `45°` | `45 * deg` |
| `√e` | `sqrt e` |
| `a + b`, `a * b`, `a · b`, … | `add a b`, `outer a b`, `dot a b`, … (every operator is a saturated application of the primitive of the same name; the names work prefix and in backticks) |
| `a ± e`, `a ±σ e` | also spelled `within a e`, `sigma a e` |
| `v.2` | `proj v 2` (a node with a literal position, §5.1) |
| `m.1.2` | `proj (proj m 1) 2` |
| `a ± b` | `uncertain bound a b` |
| `a ±σ b` | `uncertain stat a b` |
| `a to u` | `to a u`, keeping `u`'s term as the display hint |
| `-x` | `neg x`; but `-3`, or `-` applied to any constant tensor, is the negative constant itself, so a negative literal has one nominal form |
| `if c then a else b` | `if c a b` (a primitive form, lazy in both branches) |
| `[a, b, c]` | `vec [a, b, c]`; `[[…], […]]` to `mat` |
| `x ^ n` | `pow x n`, `n` an integer literal |
| `1_000_000`, `9.81`, `1e-3` | the exact rational |
| free name `m` | `Ref #hash` of what `m` currently points at |

Desugaring is total and local: no sugar needs type information, and no desugaring
step consults the codebase except the final name-to-ref resolution.

### 2.10 Component access

Vectors and matrices are indexed by **literal position only**, with a postfix dot:

```
v.0   v.1   v.2        -- components of a vector
m.1                    -- row 1 of a matrix, a vector
m.1.2                  -- row 1, column 2
```

There is no `index v i` with a computed `i`. The position is part of the type
(§4.1), so an out-of-range access is a compile-time error, and `let first v = v.0`
is a perfectly good polymorphic function that any vector of length at least one
can be passed to. Iteration over components is done with `vmap`, `dot`, `norm`
and friends, never with a loop over indices; that is how both fixed geometry
(`r.0`, `rotation.2.2`) and whole-vector computation are written in practice.

Positions are numbers only. Letter names for positions are a planned sugar at
the desugaring layer, not a lexical rule: a declaration would pin names to
positions for a scope, so that one library can use `.x .y .z`, another `.i .j .k`
or `.u .v`, and a state tuple `.pos .vel .accel`, each desugaring to the plain
numeric projection and therefore hashing identically. The design of that
declaration is open (roadmap §10).

Lexing: the dot must follow the atom immediately and be followed immediately by
digits. `v .0` and `v. 0` are errors. `1.5` is still a number because the lexer
tokenises numbers before it looks for projections, and a projection can only
follow a name, a parenthesised expression, a literal or another projection. A dot
followed by anything else (`f.g`, `f . g`) is composition; `∘` or spaces are
clearer.

---

## 3. Values, numbers and units

### 3.1 The value universe

| Static type | Runtime value | Notes |
|---|---|---|
| `Num δ` | a magnitude (§3.2) plus a dimension vector and a display-unit hint | `δ` is checked statically; the runtime dimension vector exists only for printing. `Num δ` is the rank-zero tensor `Tensor [] δ` (§3.3) |
| `Bool` | `true` or `false` | primitive because `if` and comparisons need it |
| `a -> b` | a closure: core term plus environment | first class; hashed like everything else |
| `Tensor s δ` | a flat row-major buffer of magnitudes, its shape `s`, one shared dimension vector and hint | `s` is a type-level list of lengths. `Vec n δ` and `Mat m n δ` are how `Tensor [n] δ` and `Tensor [m, n] δ` print; rotations are `Mat 3 3 1` |

There is no unit type `()` because there are no effects. There are no strings
because nothing consumes them. There is no `Int` separate from `Num`: an integer is
an exact rational with denominator 1, and positions that need an integer (the
exponent of `^`, the argument of `noise` and `gauss`) are syntactic restrictions,
not types.

Tuples are the first roadmap item after the core, because a six-element orbital
state `(r, v)` has two dimensions and cannot be a `Vec 6`. Lists come later.

### 3.2 Magnitudes: exact rationals and affine forms

A magnitude is one of two things.

**`Exact Rational`.** Produced by literals, units, `+ - * /`, integer `^`, `abs`,
`floor`, `ceil`, `round`, and by any operation whose inputs are all exact. Exact
values stay exact forever and compare exactly.

**`Affine { mid, nudges, slack }`.** An approximate value, written

```
mid + c₁·e₁ + c₂·e₂ + … + cₖ·eₖ   (± slack)
```

where `mid` and every coefficient `cᵢ` are rationals, every `eᵢ` is an unknown
number, and `slack ≥ 0` is an anonymous leftover radius. Each `eᵢ` has a name (a
*nudge id*, §3.2.4) and one of two **kinds**:

- a **bound** nudge: `eᵢ` is somewhere in `[-1, 1]`, guaranteed. Produced by
  rounding, series truncation, linearisation remainders, and `±`.
- a **statistical** nudge: `eᵢ` has mean 0 and standard deviation 1, with no hard
  limit. Produced by `±σ` and `gauss`, and used for measured constants whose
  published uncertainty is a standard uncertainty (CODATA, IAU).

The guarantee is: the true value lies in `mid ± (Σ_bound |cᵢ| + slack)` up to a
random error of standard deviation `√(Σ_stat cᵢ²)`. Both kinds propagate through
arithmetic by exactly the same rules; they differ only when a value is collapsed
for printing, comparison, budget or covariance. This is affine arithmetic in the
sense of Comba and Stolfi, with a hashed naming scheme for the noise symbols and a
kind tag so that 1σ inputs are never printed as certainties.

Why not a plain radius ("ball arithmetic") or an exact/inexact bit? Both are
degenerate affine forms with one anonymous nudge, and both suffer from the
*dependency problem*: with `x` somewhere in `[0.8, 0.9]`, interval subtraction
gives `x - x` in `[-0.1, 0.1]` because it has forgotten that both `x`s are the
same unknown. Affine forms keep the name, so `x - x` is exactly `0`.

#### 3.2.1 Linear operations are exact on nudges

Addition, subtraction, and multiplication by an exact value combine coefficients
term by term, like collecting like terms. With `x = 0.85 + 0.05·e₁`:

```
x - x        = (0.85 - 0.85) + (0.05 - 0.05)·e₁ = 0            exactly
(x + 1) - x  = 1                                              exactly
3x - x       = (2.55 - 0.85) + (0.15 - 0.05)·e₁ = 1.7 + 0.1·e₁
```

No nudge is created. Slack combines worst-case: it adds under `+` and `-`, and
scales by `|k|` under multiplication by exact `k`.

#### 3.2.2 Nonlinear operations add one fresh nudge

`x * y` with both affine, `/` by an affine value, `sqrt`, `sin`, `cos`, `tan`,
`asin`, `acos`, `atan`, `atan2`, `sinh`, `cosh`, `tanh`, `exp`, `log`, and
`norm`, `inverse`, `det`, `cross` with uncertain inputs (§3.4). The recipe:

1. Evaluate the function at the midpoint.
2. Replace the function by its tangent line (or plane) at the midpoint, which is
   linear in the existing nudges and so keeps them.
3. Bound the gap between the curve and the line over the input range. That bound
   becomes the coefficient of **one fresh nudge**.
4. Add the rigorous truncation and rounding error of the numerical evaluation to
   the same fresh nudge.

Worked example, `x * x` with `x = 0.85 + 0.05·e₁`:

```
(0.85 + 0.05·e₁)² = 0.7225 + 0.085·e₁ + 0.0025·e₁²
```

The term `0.0025·e₁²` is not of the allowed shape. Since `e₁² ∈ [0, 1]`, it lies in
`[0, 0.0025]`, which is `0.00125 ± 0.00125`. So

```
x * x = 0.72375 + 0.085·e₁ + 0.00125·e₂
```

Its range is `0.72375 ± 0.08625 = [0.6375, 0.81]`, which encloses the true range
`[0.64, 0.81]`. The `e₁` term survives, so the result still remembers it came
from `x`; only the small nonlinear leftover became an anonymous-looking `e₂`.

#### 3.2.3 Where approximation enters

Exact values become affine only at the nonlinear builtins above, at the constants
`pi` and `e`, at `sqrt` of a non-square, and at `±`, `±σ`, `noise`, `gauss`.
Approximation is
contagious through arithmetic. A program that never touches those stays exact.

#### 3.2.4 Nudge identity is content-addressed

There is no global counter. Evaluation is pure, so a nudge id must be a function
of what created it.

- **Builtin approximations**: `id = hash(builtin, operand midpoints, operand nudge
  ids and coefficients, working precision)`. Two evaluations of `sin 1` at the same
  precision produce the same nudge, so `sin 1 - sin 1 = 0`. This is correct: the
  approximation error of a deterministic algorithm on identical input is the same
  error.
- **Declared uncertainty** (`±`, `±σ`, `noise`, `gauss`): `id = hash(kind, hash of
  the enclosing top-level definition, path to the node inside it, component index,
  midpoint)`.
  Two different constants `5 ± 0.1` are independent measurements and get
  different nudges, because they sit at different definition sites. Re-evaluating
  the same `±` with the same inputs gives the same nudge.

Each nudge also records an **origin label** for the error budget: the current name
of the definition that created it (`G`, `M_earth`), or the builtin and reason
(`sin: series truncation`, `rounding @ p=24`).

#### 3.2.5 Declared uncertainty: `±`, `±σ`, `noise` and `gauss`

`noise n : Vec n 1` yields `n` fresh unit **bound** nudges as a dimensionless
vector: each component is `0 + 1·eᵢ` with `eᵢ ∈ [-1, 1]`. `gauss n : Vec n 1` does
the same with **statistical** nudges. These are the primitives. The operators are
sugar:

```
x ± err      =  x + err * noise 1      -- hard bound: |error| ≤ err, guaranteed
x ±σ err     =  x + err * gauss 1      -- standard uncertainty: σ = err
```

ASCII spellings are `+-` and `+-s`. `err` must be exact (or its own radius is
folded into slack), and both operands must share a dimension. On a vector or
matrix, both operators apply per component with independent nudges (§3.4).

Use `±` for things you can promise: a solver tolerance, a truncated series, a
manufacturing limit. Use `±σ` for things you measured or looked up with a standard
uncertainty: CODATA constants, an observed state vector with a covariance. A
bound is never silently derived from a σ, and a σ is never printed as a bound.

A function author uses `±` to declare the tolerance of their own approximation:

```
let kepler_E m e = iterate_newton m e 50 ± 1e-12
```

Callers see that error propagate like any other. There is no separate mechanism:
`±` is a core node, so it is hashed, viewable with `:view`, and versioned.

#### 3.2.6 Error budget

`:budget expr` evaluates the expression, collapses it to a scalar (for a vector
or matrix result it sums over components, or use `:budget norm v`), and lists the
nudges sorted by `|cᵢ|` with kind, origin label and share. Bound nudges share the
bound radius (`Σ|cᵢ|`); statistical nudges share the variance (`Σcᵢ²`), so their
shares are quoted as fractions of `σ²`:

```
> :budget period (7000 km)
  97.142 min  ±σ 0.006 min  (bound < 1e-9 min)
  kind   source                 contribution    share
  σ      M_earth                0.30 s          95% of σ²
  σ      G                      0.065 s          5% of σ²
  bound  sqrt: series @ p=10    < 1e-9 s       100% of bound
```

#### 3.2.7 Compaction and slack

A long computation accumulates nudges. When a value carries more than `N` nudges
(default 64), the smallest coefficients are folded into `slack`, which is a plain
worst-case radius. This is always correct and slightly loose: the folded nudges
can no longer cancel. Rounding error from midpoint arithmetic also goes into
`slack`. Slack never shrinks under any operation.

#### 3.2.8 Working precision

Midpoints are rounded to `p` decimal digits after every operation, with the
rounding error added to slack, so denominators never grow without bound. This is
the approach of the Arb library. `p` is `scale` plus guard digits (default
`scale + 4`). A value is therefore a pure function of the term and `p`. Exact
values are never rounded.

#### 3.2.9 Comparison

On exact values, comparison is exact. On affine values, `a < b` forms `a - b`,
cancels, and collapses it to `mid`, a bound radius `r` and a standard deviation
`σ`. The comparison is decided if `|mid| > r + k·σ`, where `k` is the setting
`:set sigma k` (default 3); otherwise evaluation fails with

```
cannot decide a < b at scale 20, sigma 3: a - b is 1e-5 ± 3e-21 (bound) ±σ 4e-6
```

So a comparison that depends on statistical inputs is decided at a stated
confidence, never silently, and a comparison with only bound inputs is rigorous.
`a == b` is true if `a - b` is exactly zero after cancellation (so `x == x` holds
for affine `x`), false if decided non-zero, undecidable otherwise. There is no
third truth value; error never leaks into control flow silently. Refining by
re-evaluating at higher `p` is a roadmap item; it can tighten `r`, never `σ`.

#### 3.2.10 Printing

A value prints in its display unit (§3.2.12), followed by its unit. Exact values
print in full, or truncated at `scale` digits with `…` when the decimal repeats.
An affine value is collapsed to a midpoint, a bound radius `r = Σ_bound|cᵢ| +
slack`, and a standard deviation `σ = √(Σ_stat cᵢ²)`, then printed as follows:

- `σ = 0` and `r < 10^-scale`: print `scale` digits of the midpoint and `…`. Every
  printed digit is guaranteed, because the enclosure is narrower than the last one.
- `σ = 0` otherwise: print `mid ± r`, with the midpoint rounded to the position of
  `r`'s leading digit and `r` to two significant digits.
- `σ > 0`: print `mid ±σ σ`, rounded the same way, followed by `(bound r)` when
  `r` is not negligible against `σ`. The `σ` marker is never omitted, so a 1σ band
  can never be mistaken for a certainty.

```
> 1/3
0.33333333333333333333…
> sin 1
0.84147098480789650665…
> let x = 5 ± 0.1 in x - x
0
> 5 ± 0.1
5.0 ± 0.1
> (5 ± 0.1) * (5 ± 0.1)
25.0 ± 1.0
> G
6.67430e-11 ±σ 1.5e-15 m^3 kg^-1 s^-2
> G * (2 ± 0.1)
1.335e-10 ±σ 3e-15 (bound 6.7e-12) m^3 kg^-1 s^-2
> :exact sin 1
0.841470984807896506652502321630 + 1e-30·e[bound, sin: series @ p=24]  ± 2e-31
```

`:exact e` shows the raw rational, or the midpoint, the nudge list with kinds, and
the slack.

#### 3.2.11 Units and dimensions at runtime

The seven SI base dimensions are length L, mass M, time T, current I, temperature
Θ, amount N, luminous intensity J. Their base units `m kg s A K mol cd` are
**builtins** of type `Num [L]`, `Num [M]`, and so on. Everything else is prelude
source written in the language itself and therefore hashed, viewable and
rebindable:

```
let N  = kg m / s^2
let J  = N m
let W  = J / s
let Pa = N / m^2
let km = 1000 m
let g  = kg / 1000              -- the one wrinkle: the base unit carries a prefix
```

The prelude ships: the 22 derived SI units (N, J, W, Pa, Hz, C, V, Ω, F, S, T, H,
Wb, lm, lx, Bq, Gy, Sv, kat, and `rad = 1`, `sr = 1`), the 24 SI prefixes applied to
every base and derived unit plus `L` and `g` (`km`, `mm`, `µs`, `kPa`, `GHz`, …),
and the accepted units iapetus needs: `min h day year` (Julian, 365.25 day), `AU`,
`deg arcmin arcsec`, `L`, `t`. The prefix table is generated into `prelude.ev` by a
small program, not typed by hand.

Astronomical and physical constants (`G`, `M_sun`, `M_earth`, `R_earth`) are
prelude definitions **with `±σ`** taken from CODATA and IAU standard
uncertainties, so uncertainty is present by default, carries the statistical kind,
and `:budget` can name it. CODATA publishes 1σ values, which are not hard bounds;
shipping them under `±` would let a 68% band print as a certainty, so the prelude
never does that. Exact-by-definition constants (`c`, `h`, `k_B`, `N_A`, `e_charge`
since SI 2019; IAU *nominal* `GM_earth`, `R_earth_nominal`) ship as exact rationals
with no uncertainty at all.

Runtime errors are limited to: division by zero or by an affine value whose range
contains zero; `sqrt` or `log` of a range that reaches zero or below; undecidable
comparisons; `inverse` of a possibly singular enclosure; and non-termination.
Everything else, including component access out of range, is caught statically
(§4.7).

#### 3.2.12 Display units

Values print in SI base units factored (`m s^-2`) unless they carry a *display
hint*. Rules:

- A quantity literal sets the hint: `5 km` prints as `5 km`.
- `*` and `/` combine hints syntactically: `5 km / h` prints as `5 km/h`.
- `+` and `-` keep the left operand's hint.
- Every other operation drops the hint; the result prints in base units.
- `x to u` overrides the hint with `u`, which must have the same dimension.
  `to` is overloaded over `Num`, `Vec` and `Mat`.

The hint is the *core term* of the unit expression, so it is rendered with current
names and survives name changes like any other reference.

### 3.3 Vectors, matrices and tensors

There is one aggregate type, `Tensor s δ`, where the shape `s` is a type-level
list of lengths (§4.1). A number is a rank-zero tensor, a vector has rank one, a
matrix rank two, and higher ranks (an inertia tensor's gradient) come for free.
`Num`, `Vec n` and `Mat m n` are the printer's names for ranks zero, one and
two. A literal `[a, b, c]` stacks three tensors of shape `s` into one of shape
`3 : s`, so `[[1, 2], [3, 4]]` is literally a vector of vectors, and projection
`t.i` peels one length off the front of the shape, giving a number from a
vector and a row from a matrix by the same rule. Rank-polymorphic contraction
(`einsum`) is out of scope: every primitive has a fixed-rank signature or is
polymorphic in the whole shape, so unification stays first-order.

Tensors are **homogeneous**: all components share one dimension. A position is
`Vec 3 [m]`, a velocity `Vec 3 [m/s]`, a rotation `Mat 3 3 1`. A six-element state
is the tuple `(r, v)` (roadmap), not a `Vec 6`. A state-transition matrix with
mixed dimensions is out of scope; practitioners usually non-dimensionalise to
canonical units anyway, and Hart's row/column dimension vectors are the roadmap
path if that is not enough.

Each component is an independent magnitude with its own nudge set. Because nudges
are shared by name across components, `norm (r1 - r0)` correlates error correctly
(§3.4).

Operators, each with one type (§4.2):

| Operator | Name | Meaning | Dimension rule |
|---|---|---|---|
| `+`, `-` | `add`, `sub` | elementwise on tensors of one shape | same `δ` |
| `*`, `⊗` | `outer` | tensor product; ranks add; scalar scaling is the rank-zero case | `δ₁·δ₂` |
| `·`, `@` | `dot` | contracting product: last index of the left with first of the right; dot, Mat·Vec, Mat·Mat | `δ₁·δ₂` |
| `∧`, `/\` | `wedge` | wedge product: the oriented plane of two vectors, any dimension | `δ₁·δ₂` |
| `⋆` | `star` | 3D Hodge star: a bivector to its normal vector | same `δ` |
| `×`, `><` | `cross` | 3D cross product, defined in the prelude as `star (wedge a b)`; there is no binary cross product in other dimensions, the general tool is contraction with the Levi-Civita tensor `ε`: `a × b = (ε · b) · a` | `δ₁·δ₂` |
| `⊙`, `.*` | `emul` | elementwise product | `δ₁·δ₂` |
| `⊘`, `./` | `ediv` | elementwise division | `δ₁/δ₂` |
| `/` | `div` | division by a scalar | `δ₁/δ₂` |
| `==`, `/=` | `eq`, `ne` | on tensors of one shape, and on `Bool` (the one overloaded primitive) | same type |
| `to` | `to` | on any tensor with a `Num` unit | same `δ` |

Named functions:

```
dot        : Vec n d1 -> Vec n d2 -> Num [d1 d2]
cross      : Vec 3 d1 -> Vec 3 d2 -> Vec 3 [d1 d2]
norm       : Vec n d -> Num d
transpose  : Mat m n d -> Mat n m d
inverse    : Mat n n d -> Mat n n [d^-1]
identity   : Mat n n 1
det        : Mat n n d -> Num [d^n]          -- only where n is a literal, like ^
vmap       : (Num d1 -> Num d2) -> Vec n d1 -> Vec n d2
v.i        : Vec (n + i + 1) d -> Num d      -- projection, i a literal (§2.10, §4.1)
m.i        : Mat (k + i + 1) n d -> Vec n d  -- row projection
noise      : Vec n 1                         -- n is a literal; bound nudges
gauss      : Vec n 1                         -- n is a literal; statistical nudges
covariance : Vec n d -> Mat n n [d^2]
cholesky   : Mat n n [d^2] -> Mat n n d
```

Printing factors the common unit: `[1, 2, 3] m`, `[[1, 0], [0, 1]]`. Affine
components print with their own certain digits.

### 3.4 Error on compound values

**Storage is per component; meaning is not.** Because nudges are named and shared,
a vector of affine forms over common nudges describes a *zonotope* (a sum of line
segments in space), not a box. Consider a rotation by an uncertain angle,
`t = π/4 ± 0.001` (ignoring the sub-`1e-20` nudges from `pi` and the series):

```
rotz t * [1, 0, 0] km
  x = 0.70710… km - 0.000707·e_t km
  y = 0.70710… km + 0.000707·e_t km
  z = 0
```

Both components carry the *same* `e_t` with opposite signs. The error region is a
segment tangent to the unit circle, length 2 m. A naive interval box would also
include the corner where both x and y are large, a point at radius greater than
1 km, which no rotation can produce. Now take `norm` of the result. Its tangent
plane at the midpoint is `(x·Δx + y·Δy)/|r|`, and the `e_t` coefficients cancel:
`0.7071·(-0.000707) + 0.7071·(0.000707) = 0`. The result is `1 km` plus a
second-order remainder of about `5e-7 km`. Interval arithmetic on the box would
report `1 km ± 1 m`. Affine arithmetic reports `1 km ± 0.5 mm`, and it is right.

Tuples behave the same way: `(r, v)` produced by one propagation share nudges, so a
later `r + v * dt` cancels what should cancel.

**The algebraic reason.** `Affine` is itself a container: `Affine a ≅ (a, Map
NudgeId a)`. It commutes with the shape functors up to zero coefficients:

```
Vec n (Affine Num) ≅ Affine (Vec n Num)
```

The left side is the implementation, one affine form per component. The right side
is the meaning: a midpoint vector plus one direction vector per nudge. They carry
the same information, which is why per-component storage loses nothing at the
compound level.

**Linear versus nonlinear is the organising principle.** Linear operations lift
through `Affine` exactly: `fmap f` for linear `f` is the correct lifting and
creates no nudge. Every nonlinear primitive is a controlled failure of that law:
linearise at the midpoint and add one fresh nudge whose size is exactly the amount
by which the law fails. Each builtin is therefore in one of two lists.

| Lift exactly (no new nudge) | Linearise (one new nudge) |
|---|---|
| `+`, `-` | `*`, `dot`, `cross` with both sides uncertain |
| `*` with one exact side | `/` by an affine value |
| `/` by an exact value | `sqrt sin cos tan asin acos atan atan2 sinh cosh tanh exp log` |
| `M * v`, `M * N` with one exact side | `norm`, `det`, `inverse` |
| `transpose`, `identity`, projection `.i`, `to` | `cholesky` |
| `vmap` of a function that is itself in the left column | `vmap` otherwise |
| integer `^` of an exact value, `abs` away from zero | integer `^` of an affine value (via `*`), `abs` across zero |

**`±` on a compound is an indexed map, not a plain `fmap`.** One independent nudge
per component, with the component position in the nudge identity. Without the
index, `[1, 1, 1] m ± 0.1` would give all three components the same nudge, a
segment along `(1, 1, 1)` instead of a box. The box over-approximates a radial
"known to 10 m in any direction" bound by up to √3 at the corners. A
ball-plus-zonotope representation that can express the radial bound is a roadmap
item.

**Compound-level bounds for nonlinear operations.** `inverse M` linearises as
`-M⁻¹·ΔM·M⁻¹` and needs `‖M⁻¹·ΔM‖ < 1` in a matrix norm for a rigorous remainder
(Neumann series). If the enclosure may contain a singular matrix the operation
fails with `cannot bound inverse`. `norm`, `det`, `cross` and `dot` with both
sides uncertain follow the multivariate version of the `sin` rule: gradient at the
midpoint, bounded second-order remainder.

**Structure never carries error.** Shapes and lengths are types. Tuples and
closures have no error of their own. `Bool` has none: an overlapping comparison is
a runtime error, not a third truth value.

### 3.5 Covariance: the statistical nudges, collected

Nothing extra is carried. A result `x = x₀ + Σ cᵢ·eᵢ` with vector coefficients
`cᵢ` has, over its **statistical** nudges (independent, variance 1),

```
Cov(x) = Σ_stat cᵢ cᵢᵀ = C Cᵀ
```

where `C` has the statistical `cᵢ` as columns. The nudge coefficients already
*are* a square-root factor of the covariance. Bound nudges are not part of `Cov`;
they are reported alongside as a worst-case bias box, since a rigorous bound has
no variance. Check on two nudges and two components with `c₁ = (1, 2)` and
`c₂ = (3, 0)`:

```
C = [[1, 3], [2, 0]]      C Cᵀ = [[1 + 9, 2 + 0], [2 + 0, 4 + 0]] = [[10, 2], [2, 4]]
```

Var(x₁) = 1² + 3² = 10, Var(x₂) = 2² = 4, Cov(x₁, x₂) = 1·2 + 3·0 = 2. Through
linear steps this is exactly the textbook `J P Jᵀ`, because the coefficients
transform by `J`. Through nonlinear steps it is first-order propagation, the same
approximation an extended Kalman filter makes. The fresh remainder nudge from each
nonlinear step is a *bound*, not a variance, so the view reports it separately as
a bias term.

There is no "reading" to choose: each nudge knows its kind. `±` contributes to the
bound, `±σ` to the covariance, and the printing, comparison, budget and covariance
rules all consult the kind.

**Correlated inputs are ordinary linear algebra.** A full 6×6 state covariance `P`
enters as its square-root factor `L` with `P = L Lᵀ`, split into homogeneous blocks:

```
let e = gauss 6
let r = r0 + Lr * e           -- Lr : Mat 3 6 [m]
let v = v0 + Lv * e           -- Lv : Mat 3 6 [m/s]
```

`withCovariance v P` is sugar for `v + cholesky P * gauss n` for the single-vector
case.

**Getting covariance out.** `covariance v` is an ordinary function on a homogeneous
vector. For a tuple `(r, v)` the joint 6×6 has mixed units that the v1 type system
cannot express, so the REPL view `:covariance e` prints the blocks
`Cov(r, r) : [m^2]`, `Cov(r, v) : [m^2/s]`, `Cov(v, v) : [m^2/s^2]`. This is the
strongest argument for mixed-dimension matrices on the roadmap.

`:budget` and `:covariance` are two projections of one nudge set: budget sorts
`|cᵢ|` within each kind, covariance sums `cᵢ cᵢᵀ` over the statistical kind. A
correlation matrix is a trivial third.

---

## 4. Type system

Hindley-Milner with let-polymorphism, extended with dimensions after Kennedy
("Programming Languages and Dimensions", 1996; "Types for Units-of-Measure",
2009), type-level shapes for tensors, and two deferred constraints: shape
concatenation for the products and an equality instance (§4.2).

### 4.1 Types

```
τ ::= Tensor σ δ | Bool | τ -> τ | α
σ ::= [] | ν : σ | s                   -- a shape: a list of lengths, possibly ending in a shape variable
δ ::= 1 | B | d | δ·δ | δ⁻¹          -- an abelian group, normalised
ν ::= k | n | n + k                    -- a literal, a length variable, or a variable plus a literal offset
```

`Num δ` abbreviates `Tensor [] δ`, `Vec ν δ` abbreviates `Tensor [ν] δ`, and
`Mat μ ν δ` abbreviates `Tensor [μ, ν] δ`.

**Variables are kinded.** There is one namespace of variables, each with a kind:
`Type`, `Len`, `Shape`, and `Dim` when dimensions arrive. Each kind is an index
domain with its own equational theory and its own unifier: syntactic for types,
the offset rule below for lengths, element-wise for shapes, Kennedy's algorithm
for dimensions. No term ever appears in a type, which is what keeps this on the
indexed-types side of the line (Dependent ML, GHC's `DataKinds`) and not in
dependent-type territory: lengths come only from syntax, literal element counts
and projection positions, so inference is Hindley-Milner plus constraint solving.
Typed Core (§5.3) has one kinded abstraction form and one kinded application
form for all of them.

A dimension `δ` is represented as a normalised map from atoms (a base dimension
`B ∈ {L, M, T, I, Θ, N, J}` or a dimension variable `d`) to non-zero integer
exponents. `1` is the empty map. Two dimensions are equal iff their maps are
equal.

A shape is unified element-wise: two closed shapes must have the same rank and
unify length by length; a shape variable binds to any shape (with an occurs
check). A shape variable can only stand at the tail, so `n : s` means "rank at
least one". Shape polymorphism is what lets `+`, `-`, `neg` and `vmap` have one
type for every rank: `(+) : Tensor s d -> Tensor s d -> Tensor s d`.

Lengths `ν` are a literal `k`, a variable `n`, or a variable plus a literal offset
`n + k`. The offset form exists for projection (§2.10): `t.i` gives `t` the type
`Tensor (n + i + 1 : s) d` with fresh `n` and `s`, which says "rank at least one,
first length at least `i + 1`" and nothing more, and the result is `Tensor s d`.
Unification is still first-order:

- `n + k` against a literal `j`: if `j ≥ k` then `n := j - k`, else fail. So
  `[1, 2].2` fails at check time with "position 2 is out of range for a vector of
  length 2".
- `n + k` against `m + j`: if `j ≥ k` then `n := m + (j - k)`, else `m := n + (k - j)`.
- Literals against literals: equal or fail. Variables bind as usual.

There is no other length arithmetic, so `cross` fixes `3`, `inverse` forces a
square shape, and `let first v = v.0` infers `Vec (n + 1) d -> Num d` by
unification alone.

### 4.2 Products, shape constraints and the equality instance

Nothing in the language is overloaded except equality. Every product is its own
operator with one type (core.md, "Operators across ranks"):

```
(*) (⊗)  outer : Tensor s1 δ1 -> Tensor s2 δ2 -> Tensor (s1 ++ s2) [δ1 δ2]   -- tensor product; scalar scaling is the rank-zero case
(·) (@)  dot   : Tensor (s1 ++ [n]) δ1 -> Tensor (n : s2) δ2 -> Tensor (s1 ++ s2) [δ1 δ2]   -- contracting product: dot, Mat·Vec, Mat·Mat
(∧) (/\) wedge : Vec n δ1 -> Vec n δ2 -> Mat n n [δ1 δ2]                       -- antisymmetrised outer product; the general binary product of vectors
(⋆)      star  : Mat 3 3 δ -> Vec 3 δ                                          -- 3D Hodge dual
(×) (><) cross : Vec 3 δ1 -> Vec 3 δ2 -> Vec 3 [δ1 δ2]                         -- prelude: cross a b = star (wedge a b)
(⊙) (.*) emul  : Tensor s δ1 -> Tensor s δ2 -> Tensor s [δ1 δ2]               -- elementwise
(⊘) (./) ediv  : Tensor s δ1 -> Tensor s δ2 -> Tensor s [δ1 / δ2]
(/) (÷)  div   : Tensor s δ1 -> Num δ2 -> Tensor s [δ1 / δ2]                   -- division by a scalar
```

The types of `outer` and `dot` mention shape concatenation `s1 ++ s2`, which is
not a syntactic shape when the rank of `s1` is unknown. Inference therefore
records a **shape-append constraint** `s3 ~ s1 ++ s2` and solves it as soon as it
can:

- when `s1` is closed (ends in `[]`), `s3` is the cons chain of `s1`'s lengths in
  front of `s2`, which the shape language expresses directly;
- when `s2` and `s3` are both closed, `s1` is the prefix of `s3` of rank
  `rank s3 - rank s2`, and the remainder unifies with `s2`;
- otherwise the constraint waits. Every step is first-order and unitary.

At a generalisation point a constraint whose variables are all about to be
quantified cannot wait any longer and is **defaulted**: the unknown-rank left
operand is taken to be a scalar for `outer` (so `\k v -> k * v` gets
`Num -> Tensor s -> Tensor s`) and a vector for `dot`. This is the one place the
type system guesses, it guesses the common case, and it is the rule that
dictionary passing will later remove: when data constructors exist, an
unresolved constraint becomes a parameter of the definition instead of a
default, and `\k v -> k * v` becomes polymorphic in the rank of `k`.

Equality is the single overloaded primitive. `==` and `/=` take two values of one
type `τ` and emit an **instance constraint** `Eq τ` with exactly two instances,
`Tensor s` and `Bool`. It is solved the same way: as soon as `τ` is known it is
checked, at generalisation an unresolved `τ` defaults to `Num`, and any other
type is a static error ("no equality on functions"). Lint re-checks every solved
constraint on the elaborated term, so a primitive is never evaluated at a type
its implementation cannot handle (core.md §9).

Division of a tensor by a tensor is `⊘`; `/` takes a scalar divisor only, so it
has one type too. General contraction and index permutation (`contract i j`,
`permute [p…]`, with literal indices) are roadmap items for ranks above two.
### 4.3 Types of the primitives

*Status.* Implemented: kinded variables for types, lengths, shapes and
dimensions; Kennedy unification; the seven base units as primitives; the
products of §4.2 with multiplying dimensions. `det` is on dimensionless
matrices until the length-as-exponent relation `Num [d^n]` exists. Display
units, the prelude and `to` with a display hint are the remaining pieces of
roadmap item 2.

```
literal     : Num 1
m           : Num [L]           kg : Num [M]       s : Num [T]      (etc.)
(+) (-)     : Num d -> Num d -> Num d                    (and Vec, Mat instances)
(*)         : Num d1 -> Num d2 -> Num [d1 d2]            (and the table)
(/)         : Num d1 -> Num d2 -> Num [d1 / d2]          (and the table)
(== /=)     : Num d -> Num d -> Bool                     (and Vec, Mat)
(< <= > >=) : Num d -> Num d -> Bool
(&& ||)     : Bool -> Bool -> Bool          not : Bool -> Bool
to          : Num d -> Num d -> Num d                    (and Vec, Mat)
(±) (±σ)    : Num d -> Num d -> Num d                    (and Vec, Mat)
sqrt        : Num [d^2] -> Num d
abs         : Num d -> Num d
floor ceil round : Num 1 -> Num 1
sin cos tan asin acos atan sinh cosh tanh exp log : Num 1 -> Num 1
atan2       : Num d -> Num d -> Num 1
pi e        : Num 1
e ^ n       : Num d -> Num [d^n]            -- special form, n an integer literal
noise n     : Vec n 1                        -- special form, n a natural literal
gauss n     : Vec n 1                        -- special form, n a natural literal
det         : Mat n n d -> Num [d^n]        -- special form, n known statically
v.i         : Vec (n + i + 1) d -> Num d    -- special form, i a literal position
m.i         : Mat (k + i + 1) n d -> Vec n d
```

`sin` and friends take `Num 1`, so `rad = 1` and `deg = pi / 180` in the prelude
make `sin (90 deg)` type-check and `sin (1 m)` fail. `atan2 : Num d -> Num d ->
Num 1` is the one trigonometric function that accepts a dimension, because its
two arguments share one and the result is an angle.

### 4.4 Dimension unification

To unify `δ₁` with `δ₂`, solve `δ = δ₁·δ₂⁻¹ = 1`. Write `δ` as
`d₁^x₁ ⋯ dₘ^xₘ · B₁^y₁ ⋯ Bₙ^yₙ` with `|x₁|` the smallest variable exponent.

1. **No variables** (`m = 0`): succeed iff all `yⱼ = 0`.
2. **One variable** (`m = 1`): if `x₁` divides every `yⱼ`, substitute
   `d₁ := ∏ Bⱼ^(-yⱼ/x₁)`; otherwise fail.
3. **Several variables**: if `x₁` divides every other `xᵢ` and every `yⱼ`,
   substitute `d₁ := ∏ dᵢ^(-xᵢ/x₁) · ∏ Bⱼ^(-yⱼ/x₁)` and succeed. Otherwise
   substitute `d₁ := d₁' · ∏ dᵢ^(-⌊xᵢ/x₁⌋) · ∏ Bⱼ^(-⌊yⱼ/x₁⌋)` with fresh `d₁'`
   and repeat on the result. The exponents shrink as in Euclid's algorithm, so
   this terminates.

The problem is unitary: when a unifier exists there is a single most general one.

Worked example, `sqrt (x * x)` with `x : Num d₁`. `x * x : Num [d₁^2]`. `sqrt`
expects `Num [d^2]`. Unify `d^2` with `d₁^2`: `δ = d^2 · d₁^-2`. Smallest
exponent is 2 (tie, pick `d`). 2 divides -2, so `d := d₁`. Result:
`sqrt (x * x) : Num d₁`, as it should be.

Example needing the Euclid step: unify `d₁^2 · d₂^3` with `1`. Smallest is
`x₁ = 2` on `d₁`; 2 does not divide 3. Substitute `d₁ := d₁' · d₂^(-⌊3/2⌋) =
d₁' · d₂^-1`. Now `δ = d₁'^2 · d₂^-2 · d₂^3 = d₁'^2 · d₂`. Smallest is 1 on `d₂`,
which divides 2, so `d₂ := d₁'^-2`. Composed: `d₂ = d₁'^-2`, `d₁ = d₁'^3`. Check:
`d₁'^6 · d₁'^-6 = 1`. These are exactly the solutions of `2a + 3b = 0`.

Non-unifiable example: `Num [L]` with `Num [T]`. `δ = L · T^-1` has no variables
and is not empty, so `1 m + 1 s` is rejected with

```
type error: cannot add Num [m] to Num [s]: dimensions differ by m s^-1
```

### 4.5 Inference

Standard algorithm W over Core (§5.1), dispatching to §4.4 at `Num`, `Vec`,
`Mat`, and emitting §4.2 constraints at overloaded operators. A binding group is
split into strongly connected components (§6.3); each component is inferred
monomorphically, then generalised over its free type, dimension and length
variables. Printed schemes use `a b c` for type variables, `d1 d2` for dimension
variables, `n m` for lengths, and show dimensions with base-unit symbols:

```
> :type \r -> pi * r^2
Num d1 -> Num [d1^2]
> :type (*)
Mul a b c => a -> b -> c
> :type 9.81 m/s^2
Num [m s^-2]
```

### 4.6 Known limitations

- No type annotations in v1; `:type` in the REPL is the only way to see a type.
- `^` requires a literal exponent, because `x ^ y` with a runtime `y` has no static
  dimension. `sqrt` covers the `1/2` case; a `cbrt` can follow.
- `det` requires a statically known size, for the same reason.
- Dimension polymorphism is let-polymorphism; there is no polymorphic recursion.
- Vectors and matrices are homogeneous in dimension (§3.3).
- Component access needs a literal position (§2.10). Computed indices do not exist.

### 4.7 Error reporting

**What is static.** A binding group is parsed, desugared, inferred and elaborated
as a whole, and nothing in it is stored or evaluated unless all of that succeeds.
The one-shot CLI checks a whole file first. Every error below is reported at that
point, before any arithmetic runs:

| Expression | Error | Found by |
|---|---|---|
| `1 m + 4.5 s` | dimensions differ by `m s^-1` | dimension unifier, §4.4 |
| `[1, 2] + [1, 2, 3]` | lengths 2 and 3 differ | length unification, §4.1 |
| `[1, 2].2` | position 2 out of range for length 2 | length unification, §4.1 |
| `1 + true` | `Num` versus `Bool` | HM unification |
| `sin (1 m)` | `sin` needs `Num 1`, got `Num [m]` | dimension unifier |
| `[[1, 0], [0, 1]] * [1, 2, 3]` | no instance `Mul (Mat 2 2) (Vec 3)` | overload solver, §4.2 |
| `if 1 then 2 else 3` | condition is `Num`, needs `Bool` | HM unification |
| `x ^ y` with non-literal `y` | exponent must be a literal | parser |
| `det m` with unknown size | size must be statically known | elaboration |
| `foo + 1` with no `foo` in scope | unknown name | desugaring |

Note that `1 + 4.5` is not an error: both are exact rationals of type `Num 1`.
There is no `Int` versus `Double` distinction anywhere in the language.

**What remains dynamic.** Only value-dependent failures survive to run time:
division by zero (or by an enclosure containing zero), `sqrt` or `log` of a range
reaching zero or below, an undecidable comparison, `inverse` of a possibly
singular enclosure, and non-termination. None of these is a type error, and the
type system cannot remove them without dependent types.

**Provenance.** Core has no source positions, because they would change the hash.
Instead the desugarer returns the Core term together with a *provenance table*: a
map from a path into the term (the sequence of child positions from the root) to
the surface span that produced that node, the same idea as a source map.

- Inference tracks the current path as it walks the term, and every constraint it
  emits records the path of the node that generated it. A failed unification
  therefore carries the expected and actual types *and* a path, which the table
  turns into a span.
- The dimension unifier reports the residual it could not cancel, the length
  unifier the two lengths, the overload solver the constraint it could not
  satisfy, so messages name what the user wrote:

  ```
  error at 1:1-1:11
    1 m + 4.5 s
    ^^^^^^^^^^^
    cannot add Num [m] to Num [s]: the dimensions differ by m s^-1
  ```

- Runtime errors reuse the table: a `PrimApp` that divides by zero or a comparison
  that cannot be decided reports its path, so the message points at the operation
  even though it failed during evaluation.
- Definitions already in the codebase have no source text. When an error involves
  a `Ref`, the message names the definition and its stored type
  (`period : Num [m] -> Num [s]`) instead of a span, and `:view` is how the user
  gets at its body.

The provenance table lives for one REPL interaction or one file. It is never
stored, so hashes and the codebase are unaffected, and the evaluator's type-error
cases are placeholders that elaboration makes unreachable.

---

## 5. Core and Typed Core

[core.md](core.md) is the companion document for this section: the purpose of
Core, the minimality principle it is held to, the justification for each
constructor, the invariants lint enforces, and the test any change must pass.

### 5.1 Core: the desugared language

Core is the output of desugaring and name resolution (§2.9). It is an abstract
binding tree with de Bruijn indices: binders carry a *name hint* for printing,
and hashing, equality and substitution ignore the hints. It is untyped. It is what
gets hashed.

Core is **well-scoped**: in the implementation the term type is indexed by the
number of variables in scope, `Term n`, a variable is a `Fin n`, and a binder's
body has type `Term (S n)`. A term with a dangling variable is a Haskell type
error, not a runtime one, and the evaluator's environment is a length-indexed
vector, so lookup is total. (This is the well-scoped de Bruijn idiom; Weirich's
Rebound library packages the same construction if substitution ever needs it.)
Core is *not* indexed by object-language type: it is the input to the type
checker, so it must be able to hold ill-typed terms.

```
Term n ::= Var (Fin n)                -- bound variable
         | Ref hash [idx]             -- another definition by content hash, plus cycle index
         | PrimApp name [Term n]      -- saturated primitive application
         | Lit (Tensor shape [Rational] | Bool)   -- a constant: shape and flat row-major values
         | Lam hint (Term (S n))      -- one parameter
         | App (Term n) (Term n)
         | Let hint (Term n) (Term (S n))   -- non-recursive, generalising local binding
         | If (Term n) (Term n) (Term n)    -- lazy in both branches
         | Pow (Term n) Integer       -- e ^ n
         | Noise Kind Integer         -- noise n / gauss n
         | Uncertain Kind (Term n) (Term n) -- x ± err / x ±σ err; a node, so :view shows it
         | Pack [Term n]              -- [a, b, c]: stack k tensors of shape s into shape k : s
         | Proj (Term n) Int          -- t.i, i a literal position: peel the first length
         | Cycle (Vec k hint) (Vec k (Term (k + n)))  -- k mutually recursive bodies
Kind ::= Bound | Stat
```

Rules:

- Rationals are stored in lowest terms with a positive denominator.
- **Primitives are saturated**, as PrimOps are in GHC Core. `PrimApp p args`
  always carries exactly `arity p` arguments, so `a + b` is `PrimApp "add" [a, b]`.
  A primitive used with fewer arguments is eta-expanded by the desugarer:
  `(+ 1)` is `Lam "x" (PrimApp "add" [Var 0, 1])` and a bare `sqrt` passed to
  `vmap` is `Lam "x" (PrimApp "sqrt" [Var 0])`. The arity table is static
  metadata in Core; nothing at runtime counts arguments. Overloading is still
  unresolved here; `PrimApp "add"` is the overloaded addition, and §5.3 resolves
  it to a monomorphic instance in place.
- `App` therefore only ever applies a user function (a lambda, a `Ref`, a
  variable), never a primitive.
- The quantity rule and the `let f x = …` sugar are gone; `3 m` is
  `PrimApp "mul" [Lit 3, Ref #m]` after name resolution of `m` to the prelude
  definition, and `let f x = e` is `Lam "x" e`.
- Free names are resolved to `Ref`s pointing at the hash the name has *at the
  time of definition* (§7).
- Within a `Cycle`, member `j` is referenced from inside body `i` as a variable
  bound by the `Cycle` node, so cycle members never contain their own hash.

Core is small on purpose. Every later phase (inference, elaboration, hashing,
evaluation, compilation) is written against these fifteen constructors, and
surface features are added by extending the desugarer, not the phases.

### 5.2 The nominal form

The *nominal form* of a Core term is its canonical byte encoding (§6.1): hints
dropped, variables as de Bruijn indices, rationals normalised. Two terms have the
same nominal form iff they are alpha-equivalent after name resolution. The content
hash is the SHA-256 of the nominal form.

The hash is **syntactic modulo alpha-equivalence and name resolution**. There is
no beta or eta normalisation and no constant folding: `2 + 3` and `5` are
different terms with different hashes. This keeps hashes stable under compiler
improvements and keeps `:view` output recognisable as what the author wrote.

Types, resolved overloads and elaborated dictionaries are **not** part of the
hash. They are derived from the term (§5.3) and stored beside it. Adding a type
feature later therefore never changes the identity of an existing definition.

### 5.3 Typed Core

Typed Core is Core after inference (§4) and *elaboration*. It is explicitly typed
in the manner of System F and GHC's Core, and it is what the interpreter and the
compiler consume.

*Status.* Built, without dictionary forms yet; dimensions are one more kind of
the single kinded abstraction form. Inference and elaboration are one pass;
every elaborated term is checked by `lint`, a plain type checker in the role of
GHC's Core Lint, before it is stored or evaluated; the evaluator runs Typed Core
and erases the type, length, shape and dimension abstractions;
`:core name` prints a definition with all annotations. The point of having it
now, before it changes evaluation, is the one GHC made: the surface language and
its sugar will keep changing, and a small explicitly typed core that is checked
independently is what keeps those changes honest. GHC's Core is System FC, System
F extended with type-equality coercions for GADTs and type families; ours needs
no coercions, so it is plain System F with the length index added, which is as
simple as a typed core gets.

```
TTerm ::= Var v | Ref hash [idx] | Lit …
        | Lam (hint : Type) TTerm            -- annotated binder
        | App TTerm TTerm
        | TyLam tyvar TTerm | TyApp TTerm Type        -- type abstraction/application
        | DimLam dimvar TTerm | DimApp TTerm Dim      -- dimension abstraction/application
        | LenLam lenvar TTerm | LenApp TTerm Len      -- length abstraction/application
        | DictLam (hint : Constraint) TTerm           -- dictionary parameter
        | DictApp TTerm Dict                          -- dictionary argument
        | PrimApp instance [TTerm]           -- a saturated monomorphic primitive, e.g. mul@Mat×Vec
        | Let (hint : Scheme) TTerm TTerm | If … | Pow … | Noise … | Uncertain …
        | VecLit … | MatLit … | Proj … | Cycle …
```

Elaboration does three things:

- **Explicit polymorphism.** Each generalised variable of a scheme becomes a
  `TyLam`, `DimLam` or `LenLam`; each use of a polymorphic definition becomes the
  matching applications. Dimension and length arguments are erased at runtime but
  guide the compiler (and make the pretty-printer's `:type` output exact).
- **Overload resolution.** An overloaded `PrimApp "mul" [a, b]` whose constraint
  was solved is rewritten in place to `PrimApp mul@Num×Num [a, b]`,
  `PrimApp mul@Mat×Vec [a, b]`, and so on. Because primitives are saturated this
  is a local rewrite of one node with no spine analysis. One whose constraint was
  generalised into the scheme (`Mul a b c => …`) becomes a `DictLam`, and the
  primitive inside becomes an application of a method selected from that
  dictionary.
  Call sites supply `DictApp` with the instance, or a dictionary they themselves
  received. Defaulting (§4.2) happens here, so Typed Core has no unresolved
  constraints.
- **Annotation.** Every binder carries its type or scheme, so each phase after
  elaboration is type-directed without re-inference.

Typed Core is stored in the codebase under the Core hash as derived data and is
recomputed on demand (for example when the type system changes). The interpreter
needs no runtime type information beyond value tags for printing, and the
dictionary-passing form is exactly what a compiler wants for specialisation.

---

## 6. Hashing

### 6.1 Canonical encoding

A term is encoded to bytes with `bytestring`'s `Builder`, one byte tag per
constructor, every variable-length field prefixed by its length. The hash is
SHA-256 of the encoding, displayed as a base32hex prefix: `#a3f9k`.

| Tag | Node | Payload |
|---|---|---|
| 0x00 | `Var i` | varint `i` |
| 0x01 | `Ref h idx` | 32 bytes `h`, varint `idx + 1` (0 means no index) |
| 0x02 | `PrimApp name args` | varint length, UTF-8 bytes, then each argument (count is fixed by the arity table) |
| 0x03 | `Lit tensor` | varint rank, each length as varint, then each value as sint numerator, varint denominator, row-major |
| 0x04 | `Lit bool` | one byte, 0 or 1 |
| 0x05 | `Lam t` | `t` |
| 0x06 | `App f a` | `f`, `a` |
| 0x07 | `Let e b` | `e`, `b` |
| 0x08 | `If c t e` | `c`, `t`, `e` |
| 0x09 | `Pow t n` | `t`, sint `n` |
| 0x0A | `Noise k n` | one byte kind (0 bound, 1 stat), varint `n` |
| 0x0B | `Uncertain k x err` | one byte kind, `x`, `err` |
| 0x0C | `Pack ts` | varint count, each `t` |
| 0x0D | retired | was `MatLit`; never reused |
| 0x0E | `Cycle ts` | varint count, each `t` |
| 0x0F | `Proj t i` | `t`, varint `i` |
| 0x10 | cycle-variable placeholder | no payload; only in the ordering hash of §6.2, never in a stored term |

`varint` is unsigned LEB128. `sint` is one sign byte followed by a varint byte
length and big-endian magnitude bytes, so arbitrarily large integers encode
canonically. The encoding is also the on-disk format (§7.4) and must round-trip.

The hash therefore depends on the desugaring rules and this encoding as well as
on what the user wrote; a change to either re-identifies stored definitions.
core.md, "What the hash depends on", records the consequences and the policy
decision that persistence (§10, item 6) requires.

### 6.2 Hashing cycles

Mutually recursive definitions form a cycle. Hashing follows Unison's
`hashCycle`:

1. Take one strongly connected component of the binding group.
2. Replace every reference from one member to another by a *cycle variable*.
3. Hash each body with all cycle variables replaced by one placeholder. Sort the
   members by that hash. This fixes an order that depends only on content.
4. Assign de Bruijn indices in that order and hash the whole `Cycle` term. Call it
   `H`. Member `i` is referenced from outside as `Ref H i`.

Two members whose bodies are identical up to cycle variables tie in step 3. Any
order between them produces the same `Cycle` term, so the hash is unaffected.

A component of one member that does not reference itself is a plain term, not a
cycle, and gets `Ref H` with no index.

Walkthrough:

```
let even n = if n == 0 then true  else odd  (n - 1)
let odd  n = if n == 0 then false else even (n - 1)
```

Both names are free in each other's bodies, so they form one component. After
step 2 each body is `Lam (If (… Var 0 …) (Lit b) (App (Var k) (…)))` where
`Var k` is the cycle variable and `b` is `true` or `false`. In step 3 the two
placeholder hashes differ (the literals differ). Suppose `odd` sorts first: the
order is `[odd, even]`, `odd` is member 0 and `even` is member 1. Entering the two
`let`s in the other order produces the same component, the same sort, the same
`Cycle` term and the same `H`. The namespace maps `odd ↦ Ref H 0` and
`even ↦ Ref H 1`.

### 6.3 Dependency analysis

Free names of each statement in a binding group are collected; names already in
the codebase resolve to `Ref`s immediately and are not edges. The remaining edges
feed `Data.Graph.stronglyConnComp`. Components are processed in topological
order: resolve, hash, infer types, store. A statement that names something neither
in the group nor in the codebase is an error for the whole group.

---

## 7. Codebase and names

### 7.1 Model

```
Codebase = { terms   :: Map Hash Term                -- Core, the hashed content
           , derived :: Map Hash (Scheme, TTerm)      -- inferred type, Typed Core; recomputable
           , names   :: Map Name Ref                  -- current label → reference
           , history :: Map Name [Ref]                -- newest first
           }
Ref      = Ref Hash (Maybe Int)                 -- hash plus optional cycle index
```

Entering a definition `x = e` (by `:add` or `:update`, §7.5):

1. resolves free names in `e` to their *current* refs;
2. hashes the result (§6);
3. infers its type scheme;
4. stores `(term, scheme)` under the hash, a no-op if already present;
5. points `x` at the ref and prepends to `history x`, unless it already points
   there.

Re-entering an identical body changes nothing. Entering a body that differs only
in a bound variable's name changes nothing either, because the core has no names.

### 7.2 Versioning is relabelling

Rebinding a name never changes earlier definitions that mention it, because they
hold the hash, not the name. Dependents move to a new version only by
propagation (§7.5), which is automatic on `:update` and explicit via `:upgrade`.
Trace, with propagation held back to show the stale state:

```
> let x = 5
> let y = x + 1
> :add                   -- terms: #k1 = Lit 5, #k2 = add (Ref #k1) (Lit 1);  x ↦ #k1, y ↦ #k2
> let x = 6
> :update --no-upgrade   -- #k3 = Lit 6;  x ↦ #k3;  history x = [#k3, #k1];  y untouched
> y
6                        -- y's term still refers to #k1, which is 5
> :view y
y = x#k1 + 1             -- x no longer points at #k1, so the ref is shown stale
> :todo
stale: y uses x#k1 (use :upgrade x)
> :upgrade x             -- #k4 = add (Ref #k3) (Lit 1);  y ↦ #k4
upgraded y #k2 -> #k4
> y
7
> :history y
#k4  (current)
#k2
```

A plain `:update` does the `:upgrade` step immediately and prints the same report.

`:view` renders a `Ref` by its current name when the name still points at that
hash, as `name#hash` when the name has moved on, and as `#hash` when nothing
names it. A reference into a cycle prints as `#hash.i`, and `:view` of a cycle
member shows that member's body with the other members by their current names.
Within one input, defining the same name twice is an error rather than a
rebinding: rebinding is something that happens between inputs. The same applies inside the prelude: redefining `G` to a newer CODATA
value leaves every existing function pointing at the old `G#…` until its author
re-enters it, and `:dependents G` lists them.

### 7.3 REPL commands

```
Scratch and codebase (7.5)
:add                    store pending definitions whose names are new; conflicts refer to :update
:update [--no-upgrade]  store pending definitions, re-binding existing names, then propagate
:upgrade name           move dependents still on old versions of name to its current version
:todo                   pending definitions and stale references
:scratch                list pending definitions
:forget name            drop a pending definition
:edit name              print a definition as source, ready to paste back

Inspection
:type e            inferred type scheme of e
:hash name         current ref of name
:names #hash       every name that points at the hash (current or historical)
:history name      refs the name has pointed at, newest first
:view name         pretty-print the term with refs rendered as in 7.2
:core name         print the Typed Core (5.3) with every annotation
:lint name         re-run lint on a stored definition and print its type(s)
:dependents name   definitions whose terms reference the current ref of name
:alias new old     point new at old's current ref
:unname name       remove the label; the term stays

Session
:set scale n       output digits; also sets working precision (3.2.8)
:set sigma k       confidence multiplier for comparisons on statistical values (3.2.9)
:set unicode on    pretty-print with unicode spellings (2.8); off for ASCII
:exact e           raw rational, or midpoint and nudge list
:budget e          error budget (3.2.6)
:covariance e      covariance view (3.5)
:load file         enter a file into the scratch as one binding group
:quit
```

### 7.4 CLI and persistence

```
eval                     REPL
eval 'expr'              one-shot: print the value, exit 0; on error print to stderr, exit 1
eval -f file.ev          load a file as a binding group, print bare expressions
echo 'expr' | eval       same as -f on stdin
eval --codebase DIR …    use an explicit store
```

A codebase on disk is a directory:

```
terms/<hash>       canonical bytes from 6.1
types/<hash>       the inferred scheme, text
names.log          append-only: timestamp, name, ref (or "unname")
```

The user store lives at `$XDG_DATA_HOME/eval/` and is what the daily calculator
uses. A project-local `.eval/` directory, found by walking up from the current
directory, shadows the user store; iapetus commits its `.eval/` to git. Because
terms are hash-addressed they never conflict on merge. Only `names.log` needs a
merge rule: last writer wins per name, by timestamp.

The prelude is loaded at start as an ordinary binding group, so unit definitions
and constants are hashed, viewable and rebindable like user code. Its refs are
stable across machines because its source is fixed.

### 7.5 Scratch, add, update, upgrade

The codebase is never written by typing a definition. This follows Unison, whose
users edit a scratch file that the codebase manager typechecks on every save, and
then run `add` or `update` to store what checked. The separation is what makes
versioning deliberate: trying a definition and committing a version are different
acts.

- **Scratch.** Every `let` from the REPL or a file goes into the scratch. The whole
  scratch is entered on top of the codebase as one binding group (§6.3) after each
  change, so errors appear immediately and expressions see scratch definitions
  first, then the codebase. A file defining a name twice is an error; a later REPL
  input redefining a *pending* name replaces it with a notice, because the scratch
  is a workspace, not a scope.
- **`:add`** stores pending definitions whose names are new, or whose definition is
  unchanged. A name that exists with a different definition is a conflict; the
  message points at `:update`.
- **`:update`** stores pending definitions, re-binding names that already exist,
  and then **propagates**: every current definition whose term mentions an old
  reference is rewritten to the new one (`Ref old` becomes `Ref new`, a pure term
  rewrite on Core), re-hashed, stored, and its names re-bound. Propagation runs in
  dependency order so each dependent is rewritten once, and it handles cycles,
  since a cycle is one term. Each rewritten dependent is re-typechecked against
  the codebase; one that no longer checks stays on the old version and is
  reported with the reason (`left g on #k2: expected Num -> Num, got Num`).
  `:update --no-upgrade` re-binds without propagating.
- **`:upgrade name`** is propagation on demand: every dependent still referring to
  a historical version of `name` is moved to its current version, where it checks.
- **`:todo`** lists pending definitions and stale references, so nothing is
  forgotten. `:edit name` prints a stored definition as source for the scratch.

`:add` and `:update` together are the only way a label changes. History records
every binding, `:view` shows exactly which version a definition uses, and the
semi-automated upgrade is the propagation report: what moved, and what did not
and why.

---

## 8. Evaluation

An environment-passing interpreter over **Typed Core** (§5.3). It never sees
surface syntax or unresolved overloads. Its remaining type-error cases are
unreachable for linted terms and are reported as internal errors.

- Values are the runtime forms of §3.1. A tensor of any rank is one shape at
  runtime: a flat row-major buffer of element thunks beside its list of lengths,
  with a dimension vector and display hint. A number is the rank-zero case with a
  one-element buffer. Projection is an O(1) slice, elementwise arithmetic is a
  zip over the buffer, and a component that fails to evaluate becomes a block of
  failing elements, so an error surfaces only when that component is used. The
  buffer is boxed because elements are exact rationals and later affine forms;
  an unboxed buffer is a specialisation for a future strict numeric mode, not a
  redesign. Dictionaries are values too: a record of monomorphic primitives.
- `TyLam`, `DimLam`, `LenLam` and their applications are erased: the interpreter
  steps through them without allocating.
- `DictLam` is an ordinary lambda over a dictionary value; `DictApp` applies it.
  A monomorphic `PrimApp mul@Mat×Vec [a, b]` is a direct call with its arguments
  as thunks, forced as the primitive needs them. There is no dispatch on value
  tags and no arity bookkeeping in the evaluator; the type checker has already
  guaranteed the shapes and dimensions match, so the evaluator does no dimension
  checking beyond maintaining the vector for printing.
- Closures capture the environment. Application is call-by-need: Haskell's own
  laziness supplies thunks, which `if` and recursion rely on.
- `Cycle` is evaluated by knot-tying: the list of member values is defined in terms
  of itself.
- `Ref` looks up the Typed Core of the referenced hash (elaborating it on demand if
  not yet derived) and evaluates it in the empty environment, memoised per session.
- A compiler, when it comes, starts from the same Typed Core: dictionary passing
  gives it specialisation for free, and the explicit dimension and length arguments
  tell it static shapes.
- Working precision `p` and the compaction threshold are evaluation parameters,
  passed down, never global state.
- Transcendental functions are evaluated by argument reduction and Taylor series at
  precision `p + guard`, with the truncation bound and every rounding step added to
  the fresh nudge (§3.2.2).
- Linear algebra on affine magnitudes uses Gaussian elimination with pivoting on
  midpoints; `inverse` applies the §3.4 Neumann bound.

---

## 9. Module layout and libraries

Library code in `lib/`, executable in `src/`, as `doc/style.md` requires.

```
lib/Eval/Syntax.hs           surface AST with source spans
lib/Eval/Lexer.hs            unicode normalisation and token mapping (2.8), layout rule
lib/Eval/Parser.hs           megaparsec; operator table; quantity rule; sections; where
lib/Eval/Desugar.hs          surface → Core (2.9): total, local, no types
lib/Eval/Resolve.hs          free names → refs, SCCs, cycle construction
lib/Eval/Core.hs             Core ABT with name hints; alpha-equivalence; substitution
lib/Eval/Dimension.hs        abelian group, normalisation, Kennedy unifier
lib/Eval/Type.hs             types, schemes, pretty-printing of types
lib/Eval/Infer.hs            algorithm W over Core, generalisation per component
lib/Eval/Overload.hs         closed constraint solver and defaulting
lib/Eval/TCore.hs            Typed Core (5.3)
lib/Eval/Elab.hs             Core + inference results → Typed Core
lib/Eval/Hash.hs             canonical encoding, SHA-256, cycle hashing
lib/Eval/Codebase.hs         terms, names, history; the operations of 7.1
lib/Eval/Store.hs            on-disk layout of 7.4
lib/Eval/Value.hs            runtime values
lib/Eval/Affine.hs           magnitudes: exact and affine forms, arithmetic, compaction
lib/Eval/Transcendental.hs   series evaluators with rigorous error bounds
lib/Eval/Linear.hs           vector and matrix kernels over magnitudes
lib/Eval/Eval.hs             the interpreter over Typed Core
lib/Eval/Units.hs            base dimensions, prelude generator
lib/Eval/Budget.hs           nudge attribution by kind, covariance view
lib/Eval/Pretty.hs           values, Core → surface text (unicode or ASCII), digits
lib/Eval/Repl.hs             haskeline loop and : commands
src/Main.hs                  CLI modes
data/prelude.ev              generated units and constants
```

Libraries: `megaparsec`, `text`, `containers`, `mtl`, `prettyprinter`,
`haskeline`, `cryptohash-sha256`, `bytestring`, `directory`, `filepath`; tests
with `tasty`, `tasty-hunit`, `tasty-quickcheck`.

Property tests worth writing first:

- Dimension unifier: a found unifier makes the two dimensions equal; it is
  idempotent; failure is reported only when no integer solution exists.
- Alpha-equivalent surface terms hash equal; terms that differ hash differently.
- Encode then decode is the identity on terms.
- Cycle hash is independent of the order members were entered.
- The affine enclosure always contains the true value, checked against a
  high-precision reference evaluation.
- `x - x` is exactly zero for any affine `x`.
- Compaction never shrinks the total radius.

Performance expectation: an interpreter over rational-midpoint affine forms
handles a Kepler solve or a few thousand RK4 steps interactively. Long
propagations are out of scope until the compaction threshold and precision are
tuned, and compilation is a later milestone.

---

## 10. Roadmap

1. **Core calculator.** All three representations from the start: lexer with the
   unicode table, parser, desugarer, Core with hashing, inference, elaboration to
   Typed Core, interpreter, in-memory codebase. Exact rationals only. HM without
   dimensions (`Num`, `Bool`, `->`), so Typed Core has type abstraction but no
   dimension or dictionary forms yet. One-shot CLI and a minimal REPL.
   Status: done. Inference elaborates to Typed Core, `lint` checks it, the
   evaluator runs it, and propagation (§7.5) is gated on the rewritten dependent
   re-typechecking.
2. **Dimensions.** `Dimension` module, Kennedy unifier, base-unit builtins, prelude
   generator, `to`, display hints, quantity printing. Before affine arithmetic,
   because the daily calculator needs `km/h to m/s` before it needs `sin`.
   Status: type system, base units and base-unit printing done; prelude,
   display hints and `to` remaining.
3. **Affine magnitudes.** `Affine` and `Transcendental`, all transcendental
   builtins, hash-named nudges with kinds, `±`, `±σ`, `noise` and `gauss` with
   definition-site identity,
   compaction and slack, certain-digit printing, `:exact`, `:budget`, CODATA and
   IAU constants in the prelude.
4. **Tensors.** Shape-indexed types, the product operators and their shape
   constraints, literals and printing: done. Remaining: `norm`, `inverse`,
   `det` kernels (with affine arithmetic), `covariance`, `:covariance`,
   `cholesky`, and `contract`/`permute` for ranks above two.
5. **Mutual recursion.** SCC analysis, cycle hashing, group inference.
6. **Persistence and REPL polish.** User and project-local stores, haskeline, all
   `:` commands, error messages with source spans.
7. **Tuples**, then **lists** with a `case` construct in the core.
8. **Later.** Named projection positions as a scoped sugar (`.x .y .z`,
   `.pos .vel`, §2.10); precision refinement for undecidable comparisons
   (re-evaluate at higher `p`); type annotations; user data types; mixed-dimension matrices, which
   unlocks joint state covariance as a value; ball-plus-zonotope enclosures for
   radial bounds; non-SI and affine-offset units (°C); rewrite rules that
   fuse `star (wedge a b)` back into a hand-coded 3D cross kernel and notice
   when only part of a product is consumed (laziness already avoids the
   arithmetic, not the allocation); compilation for long
   propagations.

---

## 11. Open questions

- Keep `h` for hour, given `h` is also the hecto prefix in compound names like
  `hPa`? (The prefix only ever appears attached to a unit, so there is no lexical
  clash, but readers may stumble.)
- Should `floor`, `ceil`, `round` work on quantities, as rink allows, or only on
  dimensionless values as specified here?
- Output marker: `…` for both "exact but truncated" and "approximate", or
  distinguish them, say `0.333…` versus `~0.8414…`?
- Default compaction threshold (64?) and whether `:set` should expose it.
- Default `sigma` multiplier for comparisons on statistical values: 3 (99.7%) as
  specified, or 5 to match the physics convention for "discovery"?
- Should `±` inside a function called twice with identical arguments yield one
  shared nudge (the rule in §3.2.4) or two independent ones? The current rule says
  "same inputs, same measurement"; a "measure twice" model wants independence.
- Does iapetus commit the binary `.eval/` store, or export definitions to `.ev`
  source files (text, reviewable in diffs) and treat the store as a cache?
- Should `:view` of a stale reference print `x#a3f9k` (Unison style) or `#a3f9k`
  alone?

---

## 12. Worked scenario: iapetus

An illustrative session with `:set scale 6` for brevity. Numbers are rounded for
the page; the real output follows the printing rules of §3.2.10 exactly.

```
> let mu = G * M_earth
> :type mu
Num [m^3 s^-2]
> mu
3.98602e14 ±σ 4.1e10 m^3 s^-2           -- both inputs carry ±σ from CODATA

> let period a = 2 pi * sqrt (a^3 / mu)
> :type period
Num [m] -> Num [s]
> period (7000 km) to min
97.142 ±σ 0.006 min
> :budget period (7000 km)
  97.142 min  ±σ 0.006 min  (bound < 1e-9 min)
  kind   source                 contribution    share
  σ      M_earth                0.30 s          95% of σ²
  σ      G                      0.065 s          5% of σ²
  bound  sqrt: series @ p=10    < 1e-9 s       100% of bound

> let vis_viva r a = sqrt (mu * (2 / r - 1 / a))
> :type vis_viva
Num [m] -> Num [m] -> Num [m s^-1]
> vis_viva (7000 km) (7000 km) to km/s
7.5460 ±σ 0.0004 km/s

> let rotz t = [[cos t, -(sin t), 0], [sin t, cos t, 0], [0, 0, 1]]
> :type rotz
Num 1 -> Mat 3 3 1
> rotz (90 deg) * [1, 0, 0] km
[0.000000…, 1.000000…, 0] km            -- radii ~1e-10, below 10^-scale
> let t = 45 deg ± 0.001 in rotz t * [1, 0, 0] km
[0.7071 ± 0.0007, 0.7071 ± 0.0007, 0] km
> let t = 45 deg ± 0.001 in norm (rotz t * [1, 0, 0] km)
1.000000 ± 0.0000005 km                 -- the angle error cancels in the norm

> let x = 5 ± 0.1 in x - x
0

> let e = gauss 6
> let r = [7000, 0, 0] km + Lr * e      -- Lr : Mat 3 6 [m], a covariance factor
> let v = [0, 7.5, 0] km/s + Lv * e
> :covariance (r, v)
Cov(r, r) : [m^2]        [[…], […], […]]
Cov(r, v) : [m^2 s^-1]   [[…], […], […]]
Cov(v, v) : [m^2 s^-2]   [[…], […], […]]

> let kepler_E m e = newton_E m e 50 ± 1e-12    -- a solver declaring its tolerance
```

After CODATA publishes a new `G`, the new prelude definition is entered:

```
> let G = 6.67430e-11 ±σ 1.5e-15 m^3 kg^-1 s^-2
> :update
updated G #b7x2q -> #q2m8d
upgraded mu #c40ue -> #p91sm
upgraded period #e51ka -> #0dn4r
upgraded vis_viva #ap2z1 -> #7hc9w
> :history mu
#p91sm  (current)
#c40ue
```

Every dependent moved because each still typechecks against the new `G`; the
report says so, one line per definition, and history keeps the old versions
reachable. Had a dependent stopped checking, it would have stayed on `G#b7x2q`,
`:view` would show that, and `:todo` would list it until its author fixed it and
ran `:upgrade G`. Nothing changes silently in either direction.

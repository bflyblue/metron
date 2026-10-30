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
- Temperature scales as units. °C and °F are affine, not multiplicative, so they
  are scales for points (§3.6), never units.
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
A REPL input of one line is a group of one; an input that goes on at
continuation lines (§7.3) is one group, as a file is.

```
let x = 2 + 3                   -- bind a name
let f x y = x * y + 1           -- sugar for: let f = \x y -> x * y + 1
f 3 4                           -- a bare expression: evaluate and print
```

A `let` without `in` at the top level *proposes* a definition: it goes into the
scratch (§7.5), where it is checked, hashed and usable by later expressions but
not stored. `unit name = e` is the same with the name additionally marked as a
display unit (§3.2.12), and `scale name = step at origin` a scale (§3.6). A `data`
declaration (§2.3) proposes a type the same way. `:add` and `:update` move
scratch definitions into the codebase (§7).
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

**Tuples, lists and `case`.** A tuple is `(a, b)` or `(a, b, c)`, with components
of any types; a list is `{a, b, c}` or `{}` (brackets belong to tensors, §2.4) and
`x : xs` prepends. Both are taken apart with `case`, one constructor pattern deep:

```
case p of (r, v) -> r .+ v * dt            -- a pair
case xs of {} -> 0; x : rest -> x + sum rest  -- a list, two alternatives
if c then a else b   ≡   case c of true -> a; false -> b
```

The alternatives are separated by `;` or by newlines at one indentation, as
`where` bindings are. Every alternative is a constructor pattern with variables,
or `_`, or a plain variable; nested patterns are not accepted. A `case` must be
exhaustive: `_` or a variable stands for every constructor not listed. Tuples
have no projections: `fst` and `snd` are prelude definitions by `case`, and a
six-element orbital state is `(r, v)` with two dimensions, not a `Vec 6`. Lists
are the one unbounded structure; `map`, `filter`, `foldl`, `foldr`, `length`,
`sum`, `zip`, `range` and `reverse` are prelude definitions, recursive through
`Cycle` like any other.

**Declared data types.** A `data` statement declares a type as a sum of
products, as in Haskell, with parameters of any kind:

```
data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])
data Maybe a = Nothing | Just a
data Tree a = Leaf | Node (Tree a) a (Tree a)           -- recursion through the type itself
data State n = State (Vec n [m]) (Vec n [m/s])          -- n is a length, from its use
data Reading d = Reading (Num d) (Point [K])             -- d is a dimension
structural data Pair a b = Pair a b
```

A field is a type atom: a name (`Bool`, `Num`, a parameter, a declared type
of no parameters) or a compound type in parentheses, written as `:type` prints
it: `Num [m]`, `Vec 3 [m s^-2]`, `Mat 3 3`, `Tensor [2, 3] d`, `Point [K]`,
`Point (Vec 3 [m])`, `(a, b)`, `{a}`, `a -> b`, `Maybe (Num [m])`. Inside a
dimension bracket the names are base units (`m kg s A K mol cd rad`), declared
units (`[N]`, `[km/h]`) and parameters, with `^` or superscript exponents and
`/`. A parameter's kind is read off the positions it appears in, so it needs no
annotation; using one both as a dimension and as a type is an error.

Constructors are functions and values: `Circle` has type `Num [m] -> Shape`,
`Nothing` type `Maybe a`, and `map Just xs` works. Arguments are plain
application: `Rect (3 m) (4 m)` passes two quantities, while `Rect 3 m 4 m`
would pass four arguments, the metre twice among them (§2.6). A
`case` takes a value apart one constructor deep, naming the fields in order;
`_` and variables fill in the constructors not written, as for lists. Values
print with each compound field in parentheses, `Rect (3 m) (4 m)` and
`Just (Circle (1 m))`, so that they read back whatever their units; a
record prints with its field names (below).

A type's identity is its definition: parameter kinds, the constructors' field
types in order, and the type's name as an owner stamp (§3.2.4), so two users
who declare `data Shape = …` alike share one type and `data Blob = Circle (Num
[m])` is another. `structural data` leaves the name out, so any two structural
declarations of the same shape are the same type. Constructor names and the
type name are labels in the codebase, like definition names (§7): `:unname
Circle` leaves the constructor printing as `#a3f9k.0`, `:view Shape` prints
the declaration back, and a constructor name and a definition name share one
namespace, the newer label winning (declaring `data Temp = T (Num [K])`
unnames the tesla until a `let T = …` takes the name back). A declaration is
pending in the scratch (§7.5) until `:add`, like a definition. `==` and `/=`
work on a declared type when every field of every constructor has equality
(§4.2), as on tuples and lists: `Circle (1 m) == Circle (1 m)` is true, values
built by different constructors are unequal, and a type with a function field
has no equality.

**Records.** A constructor may name its fields, which makes the type a record:

```
data Body = Body {mass :: Num [kg], pos :: Vec 3 [m], vel :: Vec 3 [m/s]}
let b = Body {mass = 5 kg, pos = [1, 2, 3] km, vel = [4, 5, 6] km/s}
b.mass                              -- 5 kg
b {vel = [0, 0, 0] m/s}             -- the same body, stopped
Body (5 kg) ([1, 2, 3] km) ([4, 5, 6] km/s)   -- positional construction still works
```

`b.mass` is a field access when the dot is glued to both sides (§2.10);
`C {f = e, …}` with a constructor builds the record and must give every field
once; `e {f = e', …}` with anything else rebuilds `e` with those fields
replaced. All of it desugars to `case` on the one constructor, so a record
is an ordinary data type to Core and to the hash, and `:view` shows the
`case`. Field names are labels like constructor names, looked up by the
field alone, so two record types cannot share a field name (the newer
declaration takes it), and `:unname .mass` removes one. Field names need a
type with one constructor, so that `b.mass` is total.

A record value prints as it is built, `Body {mass = 5 kg, pos = [1, 2, 3]
km, vel = [4, 5, 6] km s^-1}`, which reads back as the same value. The
braces delimit each field, so no field needs parentheses, and records nest:
`Pair {first = Body {…}, second = Just (Circle (1 m))}`. The printer sees
only the constructor's hash and index; the driver gives it the field labels
from the codebase, as it gives names for references (§7.2). A constructor
with no fields, or with any field unnamed (after `:unname .mass`), prints
positionally.

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
[1, 0; 0, 1]                    -- Mat 2 2, rows separated by ;
[[1, 0], [0, 1]]                -- the same matrix, nested
[1; 2]                          -- Mat 2 1, a column
[1, 2; 3, 4;; 5, 6; 7, 8]       -- Tensor [2, 2, 2]: ;; separates planes
[x, y, z] m                     -- Vec 3 [m], via the quantity rule
```

A literal is a bracketed list of expressions. Commas separate elements, `;`
separates rows, `;;` separates planes, and so on; the rank is one more than the
highest separator used, and a level that never appears is a length-one axis
(so `[1; 2]` is a 2×1 matrix, not a vector). The separator forms are sugar for
nesting: `[1, 2; 3, 4]` is `[[1, 2], [3, 4]]`, and Core sees only the nested
form. Values and `:view` print in the separator form too, except a tensor whose
outermost axis has length one (`[[1, 2, 3]]`, a 1×3 matrix), which would read
back with a lower rank and so stays nested. Elements are separated by commas, never by spaces: in a language where
juxtaposition is application and the quantity rule, `[sin x]` and `[2 pi]`
must keep meaning what they mean outside brackets. Components may be any
expression; every element must have the same shape and dimension, which the
type checker enforces.

### 2.5 Operators

From tightest to loosest:

| Level | Operators | Associativity | Notes |
|---|---|---|---|
| 10 | application, quantity rule | left | `f a b`, `3 m` |
| 9 | `^` | n/a | exponent must be an integer literal, optionally negative, so `^` cannot chain; a glued superscript is the same operator |
| 8 | unary `-` | prefix | `-x` |
| 7 | `*`/`⊗` `·`/`@` `∧`/`/\` `⊙`/`.*` `⊘`/`./` `/` | left | tensor product, contracting product, wedge product, elementwise product and division, scalar division (§4.2) |
| 7 | `×`/`><` | none | cross product |
| 6 | `+` `-` | left | overloaded over Num, Vec, Mat |
| 6 | `.+` `.-` | left | point plus amount, point from point (§3.6) |
| 5 | `±` `±σ` | none | `value ± bound`, `value ±σ stddev`, see §3.2.5 |
| 4 | `==` `/=` `<` `<=` `>` `>=` | none | ordering on Num only |
| 3 | `&&` | right | |
| 2 | `\|\|` | right | |
| 1 | `to` | none | unit conversion, lowest so `5 km / h to m/s` reads naturally |

`#label` is not an operator but a postfix on a `±`, `noise` or `gauss`
expression (§3.2.4). It is parsed after level 5 and before level 4, so it
attaches to the whole `±` expression and `x == 5 ± 0.1 #s7` labels the `±`,
not the comparison.

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

A unit atom is a unit name, or a parenthesised **unit expression**: base and
declared units (§3.2.12), numbers, and those combined with `*`, `/`, `^` and
juxtaposition. Nothing else may follow a literal without an operator. Two
literals side by side, `5 4 3` or `2 [1, 2]`, are a parse error; a name that is
not a unit, `5 a` for a matrix `a`, `2 pi`, or `5 m` under a binder `\m ->`, is
a desugaring error that says "`a` is not a unit: write the `*`". The parser
produces a `Scale` node and the desugarer, which knows which names are units,
checks it. The rule exists for units, not arithmetic: `5 * 4 * 3` and `5 * a`
are clearer written out, and `5 a` reads as a quantity to anyone who sees it. The whole quantity binds like an
application. Examples:

| Written | Means |
|---|---|
| `3 m` | `3 * m` |
| `3 m^2 kg` | `3 * m^2 * kg` |
| `9.81 m/s^2` | `(9.81 * m) / (s^2)` |
| `5 km/h` | `(5 * km) / h` |
| `[1, 0, 0] km` | `[1, 0, 0] * km` |
| `3 (m/s)` | `3 * (m / s)` |
| `5 a`, `2 pi`, `3 f x` | errors: not units |

The rule applies only to a literal on the left and units on the right. A
variable needs an explicit operator on either side: `x * km`, `5 * a`.

The rule is a parse-time rewrite to `*`. Core (§5.1) never sees it.

Inside an application there is no such grouping: `f 3 m` applies `f` to `3`
and then to `m`, exactly as `f x y` would, so a quantity in argument position
is parenthesised, `Rect (3 m) (4 m)` and `Body (5 kg) ([1, 2, 3] km)`. The
rule applies only where a literal itself is the head of the expression; a
number applied to something is not a function and is reported as such.

### 2.7 Grammar

The grammar is over canonical tokens, after the unicode mapping of §2.8.

```
program    ::= statement ( sep statement )*
sep        ::= newline-at-column-0 | ';'
statement  ::= 'let' name param* '=' expr [ 'where' bindings ]
             | 'unit' name '=' expr                      -- a display unit (3.2.12)
             | 'scale' name '=' expr 'at' expr            -- a point scale (3.6)
             | ['structural'] 'data' name param* '=' con ( '|' con )*   -- a data type (2.3)
             | expr
con        ::= name tyatom* | name '{' name '::' type ( ',' name '::' type )* '}'   -- a record (2.3)
type       ::= tyapp [ '->' type ]
tyapp      ::= name tyatom* | tyatom
tyatom     ::= name | natural | '(' type ( ',' type )* ')' | '{' type '}' | '[' bracket ']'
bracket    ::= [ product ( ',' product )* ]            -- a shape [2, 3] or a dimension [kg m^2 / s^2]
product    ::= factor+ ( '/' factor+ )*
factor     ::= ( name | natural ) [ '^' [ '-' ] natural ]
bindings   ::= binding ( sep binding )*            -- indented block
binding    ::= name param* '=' expr
param      ::= name
expr       ::= 'let' name param* '=' expr 'in' expr
             | '\' param+ '->' expr
             | 'if' expr 'then' expr 'else' expr
             | binary
binary     ::= operator-precedence parse over 'unary' using the table in 2.5,
               with `name` as an infix operator at level 9, and
               '#'label as a postfix just below ± (§3.2.4)
unary      ::= '-' unary | 'sqrt' unary | power
power      ::= app [ '^' [ '-' ] natural ]
app        ::= quantity | atom atom*
quantity   ::= number unitatom+ | vector unitatom+
unitatom   ::= atom [ '^' [ '-' ] natural ]
atom       ::= primary postfix*
postfix    ::= '.' projection | '.' name                -- glued: a component, or a record field (2.10)
             | ( '._' )+ '.' projection                -- glued: a slice along axis k = the number of '._' (2.10)
             | '{' name '=' expr ( ',' name '=' expr )* '}'    -- record construction or update (2.3)
projection ::= natural
primary    ::= number | name | 'true' | 'false'
             | '(' expr ')' | section | vector | matrix
             | '(' expr ( ',' expr )+ ')'                      -- a tuple
             | '{' [ expr ( ',' expr )* ] '}'                   -- a list
             | 'case' expr 'of' alts                       -- alts: an indented block, or ; separated
alt        ::= pattern '->' expr
pattern    ::= '(' name ( ',' name )+ ')' | '{}' | name ':' name | 'true' | 'false' | '_' | name name*
                                                  -- a lone name is a variable unless it is a constructor
section    ::= '(' operator expr ')' | '(' expr operator ')'
vector     ::= '[' [ expr ( sep expr )* ] ']'     -- sep: ',' elements, ';' rows, ';;' planes …
matrix     ::= vector                             -- [1, 2; 3, 4] or [[1, 2], [3, 4]]
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
| `°C` `°F` | `degC` `degF` | temperature scales (§3.6); `°` alone is `deg` |
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

The printer emits ASCII by default. `:set unicode on` (§7.3) switches the
exponents, `->`, `\` and `<= >= /= ||` to their unicode spellings; the
list there is the exact set for output. It also echoes each statement line in
its unicode spelling, a re-spelling of the tokens as typed (§7.3).

In the REPL a character can be typed by name, as in Julia: `\mu` then TAB
becomes `μ`, `\pm` becomes `±`, `\^2` becomes `²`. §7.3 has the details;
every entry lexes as its ASCII spelling here, or is an identifier letter.

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
| `a ± e #s7` | the same, with the unknown named `s7` (§3.2.4) |
| `v.2` | `proj v 2` (a node with a literal position, §5.1) |
| `m.1.2` | `proj (proj m 1) 2` |
| `m._.0`, `t._._.2`, `t._.0.1` | `slice 1 0 m`, `slice 2 2 t`, `proj (slice 1 0 t) 1`: the primitive applied to the axis (the number of wildcards) and the position as constants (§2.10), whatever `slice` names in scope |
| `a ± b` | `uncertain bound a b` |
| `a ±σ b` | `uncertain stat a b` |
| `a to u` | `to a u`, keeping `u`'s term as the display hint |
| `-x` | `neg x`; but `-3`, or `-` applied to any constant tensor, is the negative constant itself, so a negative literal has one nominal form |
| `if c then a else b` | `if c a b` (a primitive form, lazy in both branches) |
| `[a, b, c]` | `vec [a, b, c]`; `[[…], […]]` to `mat` |
| `x ^ n` | `pow x n`, `n` an integer literal |
| `contract i j t`, `permute [p…] t`, `slice k i t` | the primitive applied to its literal positions as constants and then `t` (§4.2). The desugarer checks that the positions are literal naturals, distinct for `contract` and a permutation of `0 .. k-1` for `permute`; a bare `contract`, `permute` or `slice` is an error, and leaving off only `t` eta-expands as for any primitive |
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
m._.0                  -- column 0 of a matrix: any row, position 0 of the next axis
t._._.2                -- position 2 of the third axis of a rank-3 tensor
```

A projection peels the first axis. To pick a position along a later axis, write
one wildcard `._` for each axis to skip, then the position: `m._.0` is column 0,
the same vector as `(transpose m).0`, and `t._._.2` drops the third axis of `t`
at position 2. Each wildcard skips exactly one axis, and the chain reads left to
right as `m.1.2` does, so `t._.0.1` slices axis 1 at 0 and then projects the
first axis of the result at 1: `(slice 1 0 t).1`. The wildcard form is sugar for
the primitive `slice k i t` (§3.3), with `k` the number of wildcards; `slice`
may also be written out, with the same literal rules as `contract`. `slice 0 i
t` is the same tensor as `t.i`, but a different term: `t.i` stays a projection.
A wildcard must be followed by a position: `m._` alone is a parse error ("a
wildcard ._ skips an axis and must be followed by a position, as in m._.0 for
column 0"). Slices apply to tensors, not to points (§3.6); a projection applies
to both. `:view` prints a slice along axis `k ≥ 1` back with wildcards
(`col = \m -> m._.0`) and `slice 0 i t` by name, so both re-parse to the same
term; `:core` prints the primitive form.

There is no `index v i` with a computed `i`. The position is part of the type
(§4.1), so an out-of-range access is a compile-time error, and `let first v = v.0`
is a perfectly good polymorphic function that any vector of length at least one
can be passed to. Iteration over components is done with `vmap`, `dot`, `norm`
and friends, never with a loop over indices; that is how both fixed geometry
(`r.0`, `rotation.2.2`) and whole-vector computation are written in practice.
Where a computation needs a component's position, `indices v` (and the
prelude's `vimap`, §3.3) gives the positions as values, `[0, 1, …, n-1]`, and
`timap` gives each component of a tensor of any rank its multi-index as a
vector; this introduces no computed indexing, because no primitive takes such a value as a
position.

Positions are numbers only. Letter names for positions are a planned sugar at
the desugaring layer, not a lexical rule: a declaration would pin names to
positions for a scope, so that one library can use `.x .y .z`, another `.i .j .k`
or `.u .v`, and a state tuple `.pos .vel .accel`, each desugaring to the plain
numeric projection and therefore hashing identically. The design of that
declaration is open (roadmap §10).

Lexing: the dot must follow the atom immediately and be followed immediately by
digits, or by a name for a record field (§2.3). `v .0` and `v. 0` are errors.
`1.5` is still a number because the lexer tokenises numbers before it looks for
projections, and a projection or field can only follow a name, a parenthesised
expression, a literal or another projection. A dot with space on either side
(`f . g`) is composition, as is `∘`; `f.g` is the field `g` of `f`. A wildcard
is a dot glued to the atom (or to the projection or wildcard before it) and
followed by `_`, where the `_` does not start an identifier; digits or another
wildcard follow, glued: `m._.0`, `t._._.2`. `m ._.0` is an error, and `x._y`
is still the composition of `x` and the name `_y`.

---

## 3. Values, numbers and units

### 3.1 The value universe

| Static type | Runtime value | Notes |
|---|---|---|
| `Num δ` | a magnitude (§3.2) plus a dimension vector and a display-unit hint | `δ` is checked statically; the runtime dimension vector exists only for printing. `Num δ` is the rank-zero tensor `Tensor [] δ` (§3.3) |
| `Bool` | `true` or `false` | a data type with two constructors; `if` is `case` on it |
| `(a, b, …)` | a tuple of values | components of any types, so a state `(r, v)` has two dimensions |
| `{a}` | a list: `{}` or `x : xs` | the one unbounded structure; lazy, so `range` and `map` stream |
| `T α…` (declared, §2.3) | a constructor and its fields, as thunks | `Shape`, `Maybe (Num [m])`, `Tree a`; the same runtime shape as tuples and lists |
| `a -> b` | a closure: core term plus environment | first class; hashed like everything else |
| `Tensor s δ` | a flat row-major buffer of magnitudes, its shape `s`, one shared dimension vector and hint | `s` is a type-level list of lengths. `Vec n δ` and `Mat m n δ` are how `Tensor [n] δ` and `Tensor [m, n] δ` print; rotations are `Mat 3 3 1` |

There is no unit type `()` because there are no effects. There are no strings
because nothing consumes them. There is no `Int` separate from `Num`: an integer is
an exact rational with denominator 1, and positions that need an integer (the
exponent of `^`, the argument of `noise` and `gauss`) are syntactic restrictions,
not types.

Tuples, lists, `Bool` and declared types are the data types; `case` (§2.3) is
how they are consumed. The built-in ones differ from declared ones only in
having syntax of their own.

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
  midpoint)`. Re-evaluating the same `±` with the same inputs gives the same
  nudge; `let f x = x ± 0.01` gives `f 2` one unknown and `f 3` another, since
  the midpoint is part of the identity, and a function's declared tolerance is
  not one number across all inputs.

  The codebase is content-addressed, so two definitions with identical text
  would be one definition and therefore one unknown. To keep `let a = 5 ± 0.1`
  and `let b = 5 ± 0.1` independent, as two parts from one batch are, the
  desugarer stamps every `±`, `noise` and `gauss` with the **name of the
  definition it is written in** (`Owner "a"`, a field of the Core node, hence
  in the hash). The stamp is never printed: `:view a` shows `5 ± 0.1`, and
  re-adding that text under the name `a` reproduces the same term, while adding
  it under another name makes a new measurement. An expression typed at the
  prompt has owner `""` and its own hash as the site. This is a deterministic,
  text-visible version of Unison's `unique type` salt: the text of a
  measurement is the whole `let name = body`, not just the body.
- **Labelled uncertainty**: `x ± r #s7` names the unknown itself. The tag
  replaces the owner stamp (`Tag "s7"`, also hashed) and the nudge's identity
  is `hash(kind, label, component)`, with no definition, path or midpoint. So
  every `±` written `#s7`, in any definition and at any midpoint, is
  `… + r·e_s7` with one `e_s7`: `5.0 ± 0.1 #s7` and `5.2 ± 0.1 #s7` differ by
  exactly `0.2`. That is how a systematic error shared by several readings, a
  sensor offset or a calibration, is written. A label may follow `±`, `±σ`,
  `noise` or `gauss` only; anywhere else it is an error. The label also names
  the source in `:budget`.

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

Add `#label` to name the unknown when several readings share one error
(§3.2.4): `let r1 = 10 mm ± 0.01 mm #batch7`.

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
can no longer cancel. Statistical nudges are never folded: a σ must not quietly
become a bound. Rounding error from midpoint arithmetic does **not** go into
slack: it joins the fresh nudge of the operation that did the rounding, whose id
is content-addressed (§3.2.4), so two evaluations of the same operation round
the same way and `sin 1 - sin 1` is still exactly `0`. Slack never shrinks under
any operation.

#### 3.2.8 Working precision

Midpoints are rounded to `p` digits after every nonlinear operation, with the
rounding error accounted for (§3.2.7), so denominators never grow without bound.
This is the approach of the Arb library. `p` is the `precision` setting plus
guard digits (default `precision + 4`). A value is therefore a pure function of
the term and `p`. Exact values are never rounded, and linear operations (`+`, `-`,
scaling by an exact value) never round, which is what keeps cancellation exact.

"`p` digits" means `p` **significant digits**: an error of at most `10^-p`
relative to the value. This is the meaning scientists and engineers give the word
(and SQL, BigDecimal and Mathematica: *precision* is significant digits,
*scale* or *accuracy* is decimal places), not bc's `scale`. Magnitudes live in SI
base units, where Planck's constant is `6.6e-34` and `G` is `6.7e-11`; with an
absolute `p`, `sqrt` of a quantity near `1e-34` would keep three significant
digits. Every series is summed to a tolerance scaled by the size of its result
(the sine of a tiny angle relative to the angle, `sinh` by its own series near
zero rather than the cancelling difference of exponentials), and midpoint rounding
follows the same rule.

#### 3.2.9 Comparison

On exact values, comparison is exact. On affine values, `a < b` forms `a - b`,
cancels, and collapses it to `mid`, a bound radius `r` and a standard deviation
`σ`. The comparison is decided if `|mid| > r + k·σ`, where `k` is the setting
`:set sigma k` (default 3); otherwise evaluation fails with

```
cannot decide comparison at sigma 3: the difference is 1e-5 ± 3e-21 ±σ 4e-6
```

So a comparison that depends on statistical inputs is decided at a stated
confidence, never silently, and a comparison with only bound inputs is rigorous.
`a == b` is true if `a - b` is exactly zero after cancellation (so `x == x` holds
for affine `x`), false if decided non-zero, undecidable otherwise. There is no
third truth value; error never leaks into control flow silently. Refining by
re-evaluating at higher `p` is a roadmap item; it can tighten `r`, never `σ`.

Any other policy is written with three accessors that take a value apart the
way printing collapses it (§3.2.10), per component on a tensor, keeping the
operand's dimension and display unit: `mid x` is the midpoint, `bound x` the
bound radius `r = Σ_bound |cᵢ| + slack`, and `sd x` the standard deviation
`σ = √(Σ_stat cᵢ²)`. On an exact value they are the value, `0` and `0`.
`mid` and `bound` are always exact; `sd` is exact when the variance is the
square of a rational (`sd (1 ±σ 0.1)` is `0.1`) and otherwise an enclosure
of the square root, as `sqrt` gives. So `bound (10 mm ± 0.1 mm)` is `0.1 mm`,
and "consistent within the bound and three σ" is

```
let consistent a b = let d = a - b in abs (mid d) <= bound d + 3 * sd d
```

#### 3.2.10 Printing

A value prints in its display unit (§3.2.12), followed by its unit. Exact values
print in full, or truncated at `precision` significant digits with `…` when the
decimal goes on (the integer part is always complete).
An affine value is collapsed to a midpoint, a bound radius `r = Σ_bound|cᵢ| +
slack`, and a standard deviation `σ = √(Σ_stat cᵢ²)`, then printed as follows:

- `σ = 0` and `r` below the last printed digit: print `precision` significant
  digits of the midpoint and `…`, zeros included. Every printed digit is
  correct to within one unit in the last place, because the enclosure is narrower
  than that place.
- `σ = 0` otherwise: print `mid ± r`, with `r` rounded to two significant digits
  (one when the second is zero) and the midpoint to the position of `r`'s last
  digit. The rounding of the midpoint is folded into `r` first, so the printed
  band still encloses the value.
- `σ > 0`: print `mid ±σ σ` the same way, followed by `(bound r)` when `r` is at
  least a hundredth of `σ`; the midpoint goes to the last digit of the coarser of
  the two. The `σ` marker is never omitted, so a 1σ band can never be mistaken for
  a certainty.

Values below `10^-4` print in scientific notation (`6.62607015e-34`), uncertain
or not, so a Planck-scale quantity is not a row of zeros.

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
25 ± 1
> let x = 5 ± 0.1 in x * x
25 ± 1
> G
6.67430e-11 ±σ 1.5e-15 m^3 kg^-1 s^-2
> G * (2 ± 0.1)
1.335e-10 ±σ 3e-15 (bound 6.7e-12) m^3 kg^-1 s^-2
> sqrt 2 * sqrt 2 == 2
error: cannot decide comparison at sigma 3: the difference is 1.0e-24 ± 1.04e-24
> :exact sin 1
0.84147098480789650665… + 2.432250…e-34·e[bound, sin]
> :exact 2 ± 0.1
2 + 0.1·e[bound, input]
```

`:exact e` shows the raw rational, or the midpoint, the nudge list with kinds and
origins (a definition's current name, `input` for the expression itself, or the
builtin), and the slack. `sqrt 2 * sqrt 2 == 2` can never be decided by any
finite-precision arithmetic; the idiom for computed values is an explicit
tolerance, `abs (a - b) < 1e-9`, which the enclosure then decides rigorously.

#### 3.2.11 Units and dimensions at runtime

The base dimensions are the seven of the SI, length L, mass M, time T, current
I, temperature Θ, amount N, luminous intensity J, **plus plane angle**, whose
base unit is the radian. Their base units `m kg s A K mol cd rad` are
**builtins** of type `Num [L]`, `Num [M]`, and so on.

The SI declares the radian dimensionless, so that `s = r θ` and `sin θ` read as
the formulas are written. We give angle a dimension instead, as Boost.Units does,
because the calculator's job is to catch the mistakes the formulas invite: `sin 1`
is an error that asks for `1 rad` or `45 deg`, angular velocity `rad/s` and
frequency `Hz` are different types that cannot be added or confused by a factor
of 2π, and `sr = rad^2` makes the photometric units honest. The price is that an
angle must be divided out where the SI quietly drops it: arc length is
`r * θ / rad` and angular velocity from a speed is `v / r * rad`, the same
bookkeeping every other dimension already asks for. Everything else is prelude
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
Wb, lm, lx, Bq, Gy, Sv, kat, `sr = rad^2`), the 24 SI prefixes applied to
every base and derived unit plus `L` and `g` (`km`, `mm`, `µs`, `kPa`, `GHz`, …),
and the accepted units iapetus needs: `min h day year` (Julian, 365.25 day), `AU`,
`deg arcmin arcsec`, `L`, `t`. The prefix table is generated into `prelude.ev` by a
small program, not typed by hand.

Measured constants are prelude definitions **with `±σ`** taken from CODATA
standard uncertainties, so uncertainty is present by default, carries the
statistical kind, and `:budget` can name it: `G = (6.67430e-11 ±σ 1.5e-15) m^3
/ (kg s^2)` (CODATA 2018). The masses are derived, `M_earth = GM_earth / G` and
`M_sun = GM_sun / G`, from the exact IAU nominal `GM` values, so their
uncertainty is G's and the budget says so (`5.97217e24 ±σ 1.3e20 kg`). Angles:
`unit deg = pi / 180 * rad`, `arcmin`, `arcsec`, so `90 deg` prints as itself
and `sin (90 deg)` is `1.00000000000000000000…`. CODATA publishes 1σ values, which are not hard bounds;
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

Magnitudes are always stored in SI base units. Values print in base units
factored (`m s^-2`) unless they carry a *display unit*, which is a product of
named units with exponents, a scale factor and a dimension. Where display units
come from:

- A definition declared with `unit` instead of `let` is a display unit:
  `unit km = 1000 * m`. The declaration is a property of the **name**, label-level
  metadata in the codebase like the binding itself, not part of the term or its
  hash. Two names may share one hash and differ here: `unit dozen = 12` and
  `let eggs = 12` are one term, `3 dozen` prints as `3 dozen` and `eggs + 1` is
  `13`, and `Bq` and `Hz` are both `1/s` yet each prints as written. What makes
  this possible is that every reference in Core carries the name the author
  wrote as a hint, ignored by the hash like a binder's name but kept in the store,
  and the evaluator asks whether *that* name is a unit. A `let` that rebinds a
  unit name (`let g = 9.81 m/s^2`) makes it a quantity; `:alias` of a unit makes
  the alias a unit; `:unname` removes the flag. If the written name has since been
  moved or removed, any current unit name of the same reference stands in, so a
  renamed unit prints under its new name. Evaluating a reference to a declared unit yields its value tagged
  with itself, so `5 km` prints `5 km` and `1 km to m` prints `1000 m`. The seven
  base units are units by construction. A `let`-bound quantity is not a unit:
  `let g = 9.81 m / s^2` prints as `9.81 m s^-2`, and so do values computed from
  it.
- `*`, `·`, `⊙`, `∧` and `^` combine display units by multiplying them; `/` and
  `⊘` divide; `5 km / h` prints as `5 km h^-1` and `(2 km)^2` as `4 km^2`. Unit
  names keep the order they were written in, so `1 V * 1 A` prints as `1 V A`.
  Units of one dimension that meet with opposite signs cancel, with their
  factor folded into the number: `2 m * 90 deg / rad` is `3.14… m`, `3 h / min`
  is `180`, `(2 km)^2 / m` is `4000 km`.
- `+` and `-` take the **smaller** of their operands' units, so that the result
  does not depend on operand order: `5 km + 3 m` and `3 m + 5 km` are both
  `5003 m`. Projection, packing, negation, `abs`, `norm`, `transpose`
  and `⋆` keep the unit; every other operation drops it.
- `x to u` replaces the display unit with `u`'s. `to` is shape-polymorphic.

The rule for which unit a result prints in, in order: an explicit `to` wins;
otherwise a declared **preference** for the value's exact dimension
(`:prefer km/h` makes every velocity print in km/h until `:unprefer km/h`; one
preference per dimension, kept in the codebase and so across sessions);
otherwise the written units, carried and simplified as above (dimensionless
results are plain numbers, units of one dimension cancel, sums take the smaller
unit); otherwise, when an operation drops the hint, SI base units. There is no
best unit for a result, only the one the user wrote or asked for, so the rule
never invents one: `1 V * 1 A` prints `1 V A`, not `1 W`, because `N m` is as
often a torque as a joule. 
A display unit whose dimension does not match the value's is ignored and base
units are printed, so the rule can never show a wrong number. Units print by
current name through the same resolution as `:view`, so a renamed unit prints
under its new name.

### 3.3 Vectors, matrices and tensors

There is one aggregate type, `Tensor s δ`, where the shape `s` is a type-level
list of lengths (§4.1). A number is a rank-zero tensor, a vector has rank one, a
matrix rank two, and higher ranks (an inertia tensor's gradient) come for free.
`Num`, `Vec n` and `Mat m n` are the printer's names for ranks zero, one and
two. A literal `[a, b, c]` stacks three tensors of shape `s` into one of shape
`3 : s`, so `[[1, 2], [3, 4]]` is literally a vector of vectors, and projection
`t.i` peels one length off the front of the shape, giving a number from a
vector and a row from a matrix by the same rule. Rank-polymorphic contraction
(`einsum`) is out of scope: every primitive has a fixed-rank signature, is
polymorphic in the whole shape, or (`contract`, `permute`) has a signature
computed from literal index positions written at the call, the way a
projection's position is, so unification stays first-order.

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
det        : Mat n n 1 -> Num 1              -- any n, dimensionless only (4.6)
vmap       : (Num d1 -> Num d2) -> Vec n d1 -> Vec n d2
vzipWith   : (Num d1 -> Num d2 -> Num d3) -> Tensor s d1 -> Tensor s d2 -> Tensor s d3
indices    : Vec n d -> Vec n                -- [0, 1, …, n-1], exact; positions as values
vimap      : (Num -> Num d1 -> Num d2) -> Vec n d1 -> Vec n d2
                                             -- prelude: vimap f v = vzipWith f (indices v) v
timap      : (Vec (rank s) -> Num d1 -> Num d2) -> Tensor s d1 -> Tensor s d2
                                             -- the multi-index as an exact vector, any rank (4.1)
v.i        : Vec (n + i + 1) d -> Num d      -- projection, i a literal (§2.10, §4.1)
m.i        : Mat (k + i + 1) n d -> Vec n d  -- row projection
noise      : Vec n 1                         -- n is a literal; bound nudges
gauss      : Vec n 1                         -- n is a literal; statistical nudges
covariance : Vec n d -> Mat n n [d^2]
cholesky   : Mat n n [d^2] -> Mat n n d
contract i j : Tensor (l0 : … : lj : s) d -> Tensor (… without i and j : s) d
                                             -- i < j literals, li = lj; a trace (§4.2)
permute [p0, …, pk-1] : Tensor (l0 : … : lk-1 : s) d -> Tensor (lp0 : … : lpk-1 : s) d
                                             -- the p a literal permutation of 0 .. k-1
slice k i  : Tensor (l0 : … : lk-1 : n + i + 1 : s) d -> Tensor (l0 : … : lk-1 : s) d
                                             -- k, i literals; written t._.i with k wildcards (§2.10)
trace      : Tensor (n : n : s) d -> Tensor s d   -- prelude: trace a = contract 0 1 a
```

`contract i j t` sums `t` over the diagonal of index positions `i` and `j`
(0-based from the front of the shape, as for `t.i`), which must have equal
lengths; the result drops both positions and keeps the dimension. `contract 0 1`
of a square matrix is its trace, so the prelude's `trace` is `Mat n n d -> Num d`
at rank two and the partial trace over the first two positions above it. The
two positions may be written in either order. The contracting product is a
contraction of the tensor product: `a · b` is `contract (r-1) r (a * b)` for `a`
of rank `r`. `permute [p0, …, pk-1] t` reorders the first `k` positions of `t`
so that position `q` of the result is position `p_q` of `t`; positions from `k`
on stay where they are, and `permute [1, 0]` is `transpose` on a matrix. Both
are linear: they create no nudge, and `contract` sums the diagonal's affine
forms, so nudges they share cancel as in `norm` (§3.4). `slice k i t` keeps
the components of `t` whose index at position `k` is `i` and drops that
position: `slice 1 0` of a matrix is its first column, and `slice 0 i t` is
`t.i`. It is written `t._.i` with `k` wildcards (§2.10), and like a projection
it gathers components without touching them, so it keeps the dimension, the
display unit and every nudge. For example:

```
> contract 0 1 [[1, 2], [3, 4]]
5
> contract 0 2 [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]
[7, 11]
> :type permute [2, 0, 1] [[[1, 2, 3], [4, 5, 6]]]
Tensor [3, 1, 2]
> :type \t -> contract 0 2 t
Tensor (n : m : n : s) d -> Tensor (m : s) d
> :type \t -> permute [2, 0, 1] t
Tensor (n : m : k : s) d -> Tensor (k : n : m : s) d
> ([1, 2; 3, 4] m)._.0
[1, 3] m
> :type \m -> m._.0
Tensor (n : m + 1 : s) d -> Tensor (n : s) d
> :type \t -> t._._.2
Tensor (n : m : k + 3 : s) d -> Tensor (n : m : s) d
```

`vzipWith f a b` is `⊙`'s general form: it applies the two-argument `f` to
each pair of components of two tensors of one shape (unequal lengths are a
type error, "lengths differ: 2 and 3"), and like `vmap` gives a result with no
display unit of its own. `indices v` is the vector
`[0, 1, …, n-1]` of exact dimensionless numbers, as long as `v`; it reads only
`v`'s length, not its components. The prelude's `vimap` combines the two, so
a map can see each component's position:

```
> vzipWith (\a b -> a * b) [1, 2, 3] [4, 5, 6]
[4, 10, 18]
> indices ([5, 6, 7] m)
[0, 1, 2]
> vimap (\i x -> i * x) [10, 20, 30]
[0, 20, 60]
> :type vimap
(Num -> Num d -> Num d1) -> Vec n d -> Vec n d1
```

The position arrives as a value, a `Num`, never as a literal, so it cannot be
used where a literal is needed: `x ^ i` is a parse error, because an exponent
is an integer literal (§2.5), and `v.i` reads a record field named `i` ("unknown
field `i`"), not a position (§2.10). `indices` is rank one only; a matrix
argument is a type error.

`timap f t` is the indexed map at any rank. For each component of `t` it
applies `f` first to the component's multi-index, a vector of exact
dimensionless naturals with one entry per axis, read off the row-major
offset, and then to the component. The index's length is the rank of `t`,
written `Vec (rank s)` (§4.1), so inside `f` the index is an ordinary vector
and `i.0`, `i.1` are ordinary projections with the usual static bound. Like
`vmap` it evaluates each result only when that component is read, takes the
result's dimension from the function, and gives the result no display unit of
its own. `vimap` stays the vector form with a scalar position; `timap` is the
general one. A diagonal mask:

```
> timap (\i x -> if i.0 == i.1 then x else 0) [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
[1, 0, 0; 0, 5, 0; 0, 0, 9]
> timap (\i x -> i.0 * x) [10, 20, 30]
[0, 20, 60]
> :type timap
(Vec (rank s) -> Num d -> Num d1) -> Tensor s d -> Tensor s d1
> let diag t = timap (\i x -> if i.0 == i.1 then x else 0) t
> :type diag
Tensor (n : m : s) -> Tensor (n : m : s)
```

The projections inside `f` are what fix how much of the shape a definition
needs: `i.1` asks for an index of length at least two, so `diag` takes a
tensor of rank at least two, and `diag [1, 2, 3]` is refused with "expected
Tensor (n : m : s), got Vec 3: a tensor of rank at least 2 against a
vector". Applied directly, `timap (\i x -> i.1 * x) [1, 2, 3]` is refused the
same way at the vector.

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
| `transpose`, `contract`, `permute`, `slice`, `identity`, projection `.i`, `to` | `cholesky` |
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

For the single-vector case `v ±σ P`, with `P : Mat n n [d^2]` the covariance
matrix, is `v + cholesky P · gauss n`: one statistical nudge per component,
identified by the definition site like every `±`, so two identical
declarations are independent and `#label` shares one. A bound has no covariance,
so `v ± P` with a matrix is a type error.

**Getting covariance out.** `covariance v : Vec n d -> Mat n n [d^2]` is an
ordinary function on a homogeneous vector, exact in the coefficients, and
`cholesky : Mat n n [d^2] -> Mat n n d` is its inverse on positive-definite
matrices (it fails with a domain error when a pivot's enclosure reaches zero).
The REPL view `:covariance e` prints the covariance of a vector, or the variance
of a number, followed by the **bound box**: each component's rigorous radius
from the bound nudges, which has no variance and is reported beside it:

```
> :covariance [cos t, sin t, 0] km        -- t = 45 deg ± 0.001 rad
covariance [0, 0, 0; 0, 0, 0; 0, 0, 0] km^2
bound box [0.00071, 0.00071, 0] km
```

For a tuple `(r, v)` the joint 6×6 has mixed units that the type system cannot
express, so it would print the blocks `Cov(r, r) : [m^2]`, `Cov(r, v) : [m^2/s]`,
`Cov(v, v) : [m^2/s^2]` once tuples exist. This is the strongest argument for
mixed-dimension matrices on the roadmap.

`:budget` and `:covariance` are two projections of one nudge set: budget sorts
`|cᵢ|` within each kind, covariance sums `cᵢ cᵢᵀ` over the statistical kind. A
correlation matrix is a trivial third.

---

### 3.6 Points and scales: affine quantities

Some quantities are **points**, not amounts: a temperature, an instant, an
electric potential, a position. Two points can be subtracted, giving the
amount between them, and an amount can be added to a point, giving another
point; but two points have no sum and a point has no double. Everything in
§3.2 to §3.5 is about amounts, which form the vector space `Num δ`. Points
form an *affine space* over it, and the language gives them their own type,
`Point δ`, and their own two operators, so that the arithmetic of points can
never be confused with the arithmetic of amounts, in the same way that the
products of §3.3 each have one symbol and one type.

| written | type | meaning |
|---|---|---|
| `p .- q` | `Point δ → Point δ → Num δ` | the amount from `q` to `p` |
| `p .+ v` | `Point δ → Num δ → Point δ` | the point `v` beyond `p` |
| `p == q`, `p < q` | `Bool` | points of one dimension compare |
| `p + q`, `k * p`, `p + v` | type errors | points have no sum, no multiple; use `.+` |

`.-` reads "from", and `.+` and `.-` sit at the precedence of `+` and `-`.
`p .+ -v` is the point `v` before `p`. The one legitimate "sum of points",
the weighted mean, is `q .+ (p .- q) / 2`.

**Scales.** A point is written and printed on a *scale*: a step unit and an
origin. The step is an ordinary unit of the amount space, the origin a point
given as an amount from the base origin:

```
unit  deltaC = K                        -- the Celsius step is the kelvin
unit  deltaF = 5/9 * K                  -- the Fahrenheit step
scale degC  = K  at 273.15 K             -- 0 °C is 273.15 K from absolute zero
scale degF  = deltaF at 459.67 deltaF    -- 0 °F is 459.67 Fahrenheit steps from it
scale J2000 = day at 2451545 day         -- an epoch: a point on the time line
scale gauge = Pa at 101325 Pa            -- gauge pressure
```

`scale name = step at origin` declares a definition whose value is a scale
(`mkScale step origin : Scale δ`) and marks the name, like `unit`, so that the
quantity rule accepts it: `20 degC` is `pointOn degC 20 : Point [K]`, the point
twenty steps up the scale from its origin, stored as `293.15 K`. `°C` and `°F`
are the unicode spellings of `degC` and `degF`. A difference carries the step
unit of the scale its operands were written on, so `77 degF .- 68 degF` is
`9 deltaF`; `20 degC .+ 5 K` and `20 degC .+ 9 deltaF` are both `25 degC`. `p to degF`
re-expresses a point on another scale of the same dimension; the point does not
change. A scale's step and origin may themselves be approximate, in which case a
point written on it carries their nudges like any other value.

**Printing.** A point prints as `(p − origin) / step` followed by the scale's
name: `25 degC`, `2451545 J2000`... that is, a point prints on the scale it
was written on, and a point whose scale has been lost prints as an amount from
the base origin in base units. Points are the one place a display offset is
needed, and the only place one is allowed: a *unit* is always a factor
(§3.2.12), which is why Celsius could never be a unit.

**Why a type and not a cleverer unit.** `20 °C + 5 °C` reads as 25 °C if the
second is a rise and as nothing if it is a temperature; written with a
factor-and-offset "unit" it silently becomes `298.15 °C`. The point/amount
distinction is the information the arithmetic needs, and it is the same
distinction as instant/duration, position/displacement, potential/potential
difference and absolute/gauge pressure. One type covers them all.

**Points over tensors.** `Point` is indexed by a shape as well as a dimension:
a position is a `Point (Vec 3 [m])`, a point of the affine space over
`Vec 3 [m]`, and its scale is a *frame*: a step unit and an origin vector,
`scale site = m at [100, 200, 0] m`. `[1, 2, 3] site` is the point with those
coordinates in the frame; `p .- q` is a displacement `Vec 3 [m]`; `p .+ v` moves
a position by a displacement; `p.0` is the first coordinate as a scalar point on
the sliced frame; `p to eci` re-expresses a position in another frame of the
same dimension. A frame here is an origin and a scale only. A frame with a
rotated basis (ECI against ECEF) is a later extension: `to` between such frames
would rotate as well as translate, which is exactly the distinction between
points and displacements that the type already enforces, since a displacement
only rotates.

## 4. Type system

Hindley-Milner with let-polymorphism, extended with dimensions after Kennedy
("Programming Languages and Dimensions", 1996; "Types for Units-of-Measure",
2009), type-level shapes for tensors, and two deferred constraints: shape
concatenation for the products and an equality instance (§4.2).

### 4.1 Types

```
τ ::= Tensor σ δ | Point σ δ | Scale σ δ | Bool | (τ, τ, …) | {τ} | T a… | τ -> τ | α
a ::= τ | σ | δ | ν                     -- an argument of a declared type T, by the kind of its parameter
σ ::= [] | ν : σ | s                   -- a shape: a list of lengths, possibly ending in a shape variable
δ ::= 1 | B | d | δ·δ | δ⁻¹          -- an abelian group, normalised
ν ::= k | n | n + k | rank s + k       -- a literal, a length variable, a variable plus a literal offset, or the rank of a shape variable plus one
```

`Num δ` abbreviates `Tensor [] δ`, `Vec ν δ` abbreviates `Tensor [ν] δ`, and
`Mat μ ν δ` abbreviates `Tensor [μ, ν] δ`. `Point σ δ` is a point of the affine space
over `Tensor σ δ` and `Scale σ δ` a scale, or frame, for writing and printing
them (§3.6). `Point [K]` prints for a scalar point and `Point (Vec 3 [m])` for
a position.

A declared type `T` (§2.3) is a type constructor with parameters of fixed
kinds, known from its definition, and `T a…` applies it to one argument per
parameter. Two applications unify when they are of the same type (the same
definition hash, §6.1) and their arguments unify kind by kind. A declared type
is identified by the hash of its definition, not by its name; the type that
inference prints as `#a3f9k` the driver renames (§7.2).

**Variables are kinded.** There is one namespace of variables, each with a kind:
`Type`, `Len`, `Shape`, and `Dim` when dimensions arrive. Each kind is an index
domain with its own equational theory and its own unifier: syntactic for types,
the offset rule below for lengths, element-wise for shapes, Kennedy's algorithm
for dimensions. No term ever appears in a type, which is what keeps this on the
indexed-types side of the line (Dependent ML, GHC's `DataKinds`) and not in
dependent-type territory: lengths come only from syntax, literal element counts,
projection positions, the literal index positions of `contract`,
`permute` and `slice` (§4.2), and the ranks of shapes (below), so inference is
Hindley-Milner plus constraint solving.
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
A slice along a later axis (`t._.i`, `slice k i t`, §2.10) uses the same offset
one axis further in: `t` gets `Tensor (l0 : … : lk-1 : n + i + 1 : s) d` with
fresh `l0 … lk-1`, `n` and `s`, and the result is `Tensor (l0 : … : lk-1 : s) d`,
so `\m -> m._.0` is `Tensor (n : m + 1 : s) d -> Tensor (n : s) d`. When the
length at axis `k` is already a known literal too small for `i`, the error says
so in the projection's words, naming the axis: `[1, 2; 3, 4]._.2` is "position 2
is out of range for axis 1 of length 2". When the rank is known and too small,
the error is the rank message of `contract` (§4.2), not a shape mismatch:
`[1, 2, 3]._.0` is "slice 1 0 needs a tensor of rank at least 2, got Vec 3".
Through a polymorphic definition (`let col2 m = m._.2` applied to a 2×2 matrix)
the offset rule reports the length as too short, as it does for `v.2`.
Unification is still first-order:

- `n + k` against a literal `j`: if `j ≥ k` then `n := j - k`, else fail. So
  `[1, 2].2` fails at check time with "position 2 is out of range for a vector of
  length 2".
- `n + k` against `m + j`: if `j ≥ k` then `n := m + (j - k)`, else `m := n + (k - j)`.
- Literals against literals: equal or fail. Variables bind as usual.

There is no other length arithmetic, so `cross` fixes `3`, `inverse` forces a
square shape, and `let first v = v.0` infers `Vec (n + 1) d -> Num d` by
unification alone.

**The rank of a shape.** `rank` is the first, and so far the only, type-level
function: `rank σ` is the number of lengths in `σ`, a length, and it exists so
that `timap` (§3.3) can type its index as `Vec (rank s)`. It is allowed
because it always normalises to a residual over one shape variable plus a
literal offset: `rank [] = 0`, `rank (ν : σ) = rank σ + 1`, and `rank s` of a
shape variable stays as it is, so a length is still a literal, a variable plus
an offset, or `rank s + k`. When `s` is bound the rank is normalised again, so
`rank s` with `s := (n : m : s1)` becomes `rank s1 + 2`, and with `s := [2, 3]`
the literal `2`. Unification therefore stays first-order; its rules for `rank`
are in §4.2. It prints parenthesised where an offset form is, `Vec (rank s)`
and `Vec (rank s + 1)`, and it is not part of the written type syntax.

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

**Ranks.** A length `rank s + k` (§4.1) unifies with another length by
binding a variable outright wherever it can, because a rank says exactly how
many lengths a shape has and nothing about the lengths themselves:

- `rank s + k` against a literal `j`: if `j ≥ k` then `s` is `j - k` fresh
  length variables, `s := [n1, …, n(j-k)]`, else fail ("a rank of at least 3
  cannot be 2"). The lengths stay unknown; only the rank is fixed.
- `rank s + k` against `n + m`: if `k ≥ m` then `n := rank s + (k - m)`.
  Otherwise the rank must be at least `m - k`, which a shape says by its
  leading lengths: `s := (n1 : … : n(m-k) : s1)` with fresh variables, and then
  `n := rank s1`. No length ever carries a negative offset, so "at least" is
  never lost: in `timap (\i x -> i.1 * x) t` the projection gives `i : Vec (n
  + 2)`, and unifying that with `Vec (rank s)` makes `t : Tensor (n1 : n2 :
  s1) d`.
- `rank s + k` against `rank s + j`: the offsets must be equal.
- `rank s + k` against `rank s' + j` for another shape variable: the
  variable with the smaller offset gains the difference as leading lengths,
  as above, and what remains, `rank s1
  = rank s2` between two unbound variables, has no first-order solution. It is
  recorded as a pending **rank equation**, beside the shape-append
  constraints, and solved as soon as either shape is bound.

A rank equation still pending at a generalisation point, with all its
variables about to be quantified, is a static error: "two tensors here must
have the same rank, which a generalised type cannot say; give one of them a
known rank". It is not defaulted, because any rank picked would be a guess,
and it is not dropped, because nothing in the scheme would then make a use
site check it. It arises typically when one index function is shared by two maps
of unknown shapes, as in `\f t u -> (timap f t, timap f u)`. Everything else
about a rank is in the type itself, so a definition over `timap` generalises
with no constraint: `\t -> timap (\i x -> i.0 * x) t` is `Tensor (n : s) d ->
Tensor (n : s) d`, and `\t -> timap (\i x -> dot i i * x) t`, whose index
function works at any length, is `Tensor s d -> Tensor s d`. Lint checks a
use of `timap` like any fixed scheme: the recorded type, with the rank
normalised, must be an instance of `timap`'s, so the index length must be the
rank of the recorded shape.

Equality is the single overloaded primitive. `==` and `/=` take two values of one
type `τ` and emit an **instance constraint** `Eq τ`. Its instances are
`Tensor s`, `Bool` and `Point s d`, and structured data whose components have
equality: a tuple when every component does, a list when its element does,
and a declared type `T τ…` when every field of every constructor, at those
arguments, does. Values of data types are equal when their constructors are
the same and their fields are pairwise equal. For a declared type the
instance is derived structurally: a recursive occurrence of `T` in its own
fields is the instance being derived (coinductively), and which of `T`'s
parameters need equality is a least fixed point over the fields, so `Eq (Tree
τ)` reduces to `Eq τ`, `Eq Shape` holds outright, and a nested type such as
`data N a = Z a | S (N (a, a))` is decided without unfolding. It is solved
the same way: as soon as `τ` is known it is checked, at generalisation an
unresolved `τ` defaults to `Num`, and any other type is a static error ("no
equality on Num -> Num"; a declared type with a function field has none). Lint re-checks every solved
constraint on the elaborated term, so a primitive is never evaluated at a type
its implementation cannot handle (core.md §9).

Division of a tensor by a tensor is `⊘`; `/` takes a scalar divisor only, so it
has one type too.

**Contraction and permutation with literal positions.** `contract i j` and
`permute [p0, …, pk-1]` work at any rank. Their positions are part of the type,
as a projection's is (§4.1), so the desugarer insists on literals the way it
does for `noise n`: each index of `contract` is a literal natural, the two are
distinct, and `permute`'s argument is a literal vector that is a permutation of
`0 .. k-1` with `k ≥ 1`. Anything else is a desugaring error that quotes the
rule ("the positions of contract must be literal natural numbers: contract i j
t", "contract pairs two different positions, not position 0 with itself",
"permute [0, 0] is not a permutation of 0 .. 1", "permute takes a literal
vector of natural numbers, a permutation of 0 .. k-1 with k ≥ 1"). A bare
`contract` or `permute`, without its positions, is the same kind of error;
leaving off only the tensor is an ordinary eta expansion: `contract 0 1` alone
is `\x -> contract 0 1 x`. The positions stay arguments of the
primitive, constants in Core, so no Core form is needed (core.md §5).

The scheme is computed from the literals, each use with fresh variables, and is
then an ordinary first-order scheme. With `a = min i j` and `b = max i j`:

```
contract i j          : Num -> Num -> Tensor (l0 : … : lb : s) d -> Tensor (l0 : … : lb without positions a and b : s) d
                        where lb is the variable la: the paired lengths are one length
permute [p0, …, pk-1] : Vec k -> Tensor (l0 : … : lk-1 : s) d -> Tensor (lp0 : … : lpk-1 : s) d
slice k i             : Num -> Num -> Tensor (l0 : … : lk-1 : n + i + 1 : s) d -> Tensor (l0 : … : lk-1 : s) d
```

`slice k i` (§2.10) follows the same rules: the axis `k` and position `i` are
literal naturals ("the axis and position of slice must be literal natural
numbers: slice k i t"), a bare `slice` is an error, and the sliced axis has the
projection's offset length (§4.1).

The leading `Num` and `Vec k` are the literal positions themselves. Because
the paired positions of `contract` share one length variable, unequal lengths
are an ordinary length-unification failure: `contract 0 1 [[1, 2, 3], [4, 5,
6]]` reports "expected Tensor (n : n : s) d, got Mat 2 3: lengths differ: 2 and
3". A tensor whose rank is known and too small for the positions is reported as
such, rather than as the shape mismatch beneath it: `contract 0 2` on a matrix
is "contract 0 2 needs a tensor of rank at least 3, got Mat 2 2", and likewise
`permute [2, 0, 1]`. When the rank is not yet known the scheme simply asks for
at least `b + 1` (or `k`) positions, and a later use that cannot supply them
fails with the shape mismatch. Positions beyond the rank are therefore always
type errors, never runtime ones. Lint recomputes the scheme from the `TLit`
arguments of the elaborated `PrimApp` and checks that the recorded type is an
instance of it, as it does for every fixed scheme.
### 4.3 Types of the primitives

*Status.* Implemented: kinded variables for types, lengths, shapes and
dimensions; Kennedy unification; the seven base units as primitives; the
products of §4.2 with multiplying dimensions. `det` is on dimensionless
matrices of any size until the length-as-exponent relation `Num [d^n]`
exists (§4.6). Display
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
mid         : Tensor s d -> Tensor s d               -- per component: the midpoint, exact (3.2.9)
bound       : Tensor s d -> Tensor s d               -- per component: Σ_bound |cᵢ| + slack, exact
sd          : Tensor s d -> Tensor s d               -- per component: √(Σ_stat cᵢ²), exact or enclosed
floor ceil round : Num 1 -> Num 1
sin cos tan : Num [rad] -> Num 1
asin acos atan : Num 1 -> Num [rad]
sinh cosh tanh exp log : Num 1 -> Num 1
atan2       : Num d -> Num d -> Num [rad]
mkScale     : Num d -> Tensor s d -> Scale s d          -- step, origin (3.6)
pointOn     : Scale s d -> Tensor s 1 -> Point s d      -- what the quantity rule builds for `20 degC`, `[1, 2, 3] site`
pointAdd    : Point s d -> Tensor s d -> Point s d      -- `.+`
pointSub    : Point s d -> Point s d -> Tensor s d      -- `.-`
toScale     : Point s d -> Scale s d -> Point s d       -- `p to s` when s is a scale
p.i         : Point (n + i + 1 : s) d -> Point s d      -- a coordinate is a point
covariance  : Vec n d -> Mat n n [d^2]                  -- Σ cᵢcᵢᵀ over the statistical nudges (3.5)
cholesky    : Mat n n [d^2] -> Mat n n d
vzipWith    : (Num d1 -> Num d2 -> Num d3) -> Tensor s d1 -> Tensor s d2 -> Tensor s d3   -- per component pair, no display unit (3.3)
indices     : Vec n d -> Vec n                          -- [0, 1, …, n-1], exact; the argument's components are not read
timap       : (Vec (rank s) -> Num d1 -> Num d2) -> Tensor s d1 -> Tensor s d2   -- the multi-index, exact, then the component; no display unit (3.3, 4.1)
x ± e, x ±σ e : Tensor s d -> Num d | Tensor s d -> Tensor s d   -- per component (3.4)
v ±σ P      : Vec n d -> Mat n n [d^2] -> Vec n d       -- a vector with covariance P (3.5)
pi e        : Num 1
e ^ n       : Num d -> Num [d^n]            -- special form, n an integer literal
noise n     : Vec n 1                        -- special form, n a natural literal
gauss n     : Vec n 1                        -- special form, n a natural literal
det         : Mat n n 1 -> Num 1            -- a plain primitive, any n; dimensionless only (4.6)
v.i         : Vec (n + i + 1) d -> Num d    -- special form, i a literal position
m.i         : Mat (k + i + 1) n d -> Vec n d
contract i j t : Tensor (l0 : … : lj : s) d -> Tensor (… without i and j : s) d   -- special form, i ≠ j literal naturals, li = lj (4.2)
permute [p…] t : Tensor (l0 : … : lk-1 : s) d -> Tensor (lp0 : … : lpk-1 : s) d -- special form, a literal permutation of 0 .. k-1 (4.2)
slice k i t : Tensor (l0 : … : lk-1 : n + i + 1 : s) d -> Tensor (l0 : … : lk-1 : s) d -- special form, k and i literal naturals; t._.i (2.10, 4.1)
```

The circular functions take an angle and their inverses return one (§3.2.11):
`rad` is a base unit and `deg = pi / 180 * rad`, so `sin (90 deg)` type-checks,
`sin (1 m)` fails, and so does `sin 1`, with a message that asks for `1 rad` or
`45 deg`. `atan2 : Num d -> Num d -> Num [rad]` accepts any one dimension for
its two arguments. The hyperbolic functions, `exp` and `log` take plain numbers.

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
- `det` is on dimensionless matrices only. Its natural type, `Mat n n d -> Num
  [d^n]`, needs a length as a dimension exponent, which the type system does
  not have. So `det : Mat n n 1 -> Num 1` (`:type det` prints `Mat n n ->
  Num`): it is polymorphic in `n` with no static size check, so `let d a =
  det a` generalises and works at every size. A matrix with a unit is a type
  error ("expected Mat n n, got Mat 2 2 [m]"); divide the unit out first, as
  in `det (a / (1 m))`, and multiply by `m^n` for the size at hand.
- Dimension polymorphism is let-polymorphism; there is no polymorphic recursion.
- `rank` is the only type-level function, and a type cannot say that two
  unknown shapes have the same rank: a definition that needs that, such as
  `\f t u -> (timap f t, timap f u)`, is refused at generalisation (§4.2).
- Vectors and matrices are homogeneous in dimension (§3.3).
- Component access needs a literal position (§2.10). Computed indices do not exist.
  The same holds for the positions of `contract` and `permute` (§4.2): a
  function cannot take them as parameters, so `\i -> contract i 0 t` is an
  error.

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
| `det a` with `a : Mat 2 2 [m]` | expected `Mat n n`, got `Mat 2 2 [m]` | dimension unifier |
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
the surface span that produced that node, the same idea as a source map. The
table also carries *hints*: advice the desugarer attaches to a span while it
still sees the syntax, printed under a type error that lands there. The one
hint so far: a literal argument followed by a unit name (`Rect 3 m 4 m`) is two
arguments, and the error says to write `(3 m)` (§2.6).

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
         | Lit (Tensor shape [Rational])   -- a constant tensor: shape and flat row-major values
         | Lam hint (Term (S n))      -- one parameter
         | App (Term n) (Term n)
         | Let hint (Term n) (Term (S n))   -- non-recursive, generalising local binding
         | Con con [Term n]           -- a saturated data constructor
         | Case (Term n) [Alt n]      -- one alternative per constructor, canonical order, lazy in the bodies
         | Pow (Term n) Integer       -- e ^ n
         | Noise Kind Integer         -- noise n / gauss n
         | Uncertain Kind (Term n) (Term n) -- x ± err / x ±σ err; a node, so :view shows it
         | Pack [Term n]              -- [a, b, c]: stack k tensors of shape s into shape k : s
         | Proj (Term n) Int          -- t.i, i a literal position: peel the first length
         | Cycle (Vec k hint) (Vec k (Term (k + n)))  -- k mutually recursive bodies
Alt n  ::= Alt con (Vec k hint) (Term (k + n))   -- binds the constructor's k fields
con    ::= Builtin name                    -- True, False, Tuple, Nil, Cons
         | UserCon hash i                  -- constructor i of the declared type with that definition hash
Kind ::= Bound | Stat
```

`if c then a else b` is `Case c [Alt False [] b, Alt True [] a]`; `true` is
`Con True []`; `(a, b)` is `Con Tuple [a, b]` (the arity is the argument count);
`{a, b}` is `Con Cons [a, Con Cons [b, Con Nil []]]`. Alternatives follow the
constructors' declaration order (`False, True`; `Nil, Cons`; a declared
type's as written) and cover every constructor of the scrutinee's type; a
surface `_` is expanded into the missing alternatives, so Core has no default
case. A declared constructor is referenced by its type's definition hash and
its position, never by name, so renaming a constructor changes no term (§7.2)
and a term's hash depends on the type's definition, not on what it is called.

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
| 0x04 | retired | was `Lit bool`; read by the format-2 decoder as `Con True/False`, never written |
| 0x05 | `Lam t` | `t` |
| 0x06 | `App f a` | `f`, `a` |
| 0x07 | `Let e b` | `e`, `b` |
| 0x08 | retired | was `If c t e`; read by the format-2 decoder as a `Case` on `Bool`, never written |
| 0x09 | `Pow t n` | `t`, sint `n` |
| 0x0A | `Noise k l n` | one byte kind (0 bound, 1 stat), label, varint `n` |
| 0x0B | `Uncertain k l x err` | one byte kind, label, `x`, `err` |

A label is one byte (0 owner, 1 tag) and the text. In the *storage* encoding
(§7.4) every `Ref` is followed by the name the author wrote, and every binder
by its name hint; the canonical encoding, and so the hash, has neither. The owner stamp is the
name of the enclosing definition (§3.2.4), so the hash of a definition that
declares uncertainty depends on its name; nothing else in the hash does.
| 0x0C | `Pack ts` | varint count, each `t` |
| 0x0D | retired | was `MatLit`; never reused |
| 0x0E | `Cycle ts` | varint count, each `t` |
| 0x0F | `Proj t i` | `t`, varint `i` |
| 0x10 | cycle-variable placeholder | no payload; only in the ordering hash of §6.2, never in a stored term |
| 0x11 | `Con con args` | constructor reference, varint count, each argument |
| 0x12 | `Case s alts` | `s`, varint count, each alternative: constructor reference, varint `k`, (`k` hints in the storage encoding), body at depth `+ k` |

A constructor reference is the text name for a built-in constructor, or an
empty text followed by the 32-byte definition hash of the declared type and
the varint position of the constructor in it. Built-in constructors therefore
encode as they did before declared types existed, and no format bump was
needed.

A declared type (§2.3) is hashed separately, from its own canonical encoding:
varint parameter count and one kind byte per parameter (0 type, 1 length, 2
shape, 3 dimension); varint constructor count, and per constructor a varint
field count and each field type; then the label (0 owner and the type name,
or 1 and an empty text for `structural`). Types use tags of their own:

| Tag | Type | Payload |
|---|---|---|
| 0x20 | `Bool` | |
| 0x21 | `Tensor σ δ` | shape, dimension |
| 0x22 | `Point σ δ` | shape, dimension |
| 0x23 | `Scale σ δ` | shape, dimension |
| 0x24 | tuple | varint count, each type |
| 0x25 | list | element type |
| 0x26 | `a -> b` | `a`, `b` |
| 0x27 | variable | varint id (a parameter: 0 .. k-1) |
| 0x28 | `T a…` | 32-byte hash, varint count, each argument as a kind byte and a type, length, shape or dimension |

A shape is 0 for `[]`, 1 then a length and a shape, or 2 and a variable id; a
length is 0 and a varint literal, 1, a variable id and a varint offset, or 2,
a shape variable id and a varint offset for `rank s + k` (§4.1; appended, so
earlier encodings decode unchanged); a
dimension is a varint atom count and per atom 0 and a base-dimension byte or 1
and a variable id, then the sint exponent. A recursive occurrence of the type
being declared is `0x28` with the all-zero hash, so the definition never
contains its own hash.

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
           , typeDefs  :: Map Hash TypeDef           -- declared types by definition hash (2.3)
           , typeNames :: Map Name Hash              -- type labels
           , conNames  :: Map Name (Hash, Int)       -- constructor labels: a type and a position
           , fieldNames :: Map Name (Hash, Int, Int) -- record field labels: type, constructor, position
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
:edit name              print a definition, or a data declaration, as source, ready to paste back

Inspection
:ls [glob] [--all|--units|--scales|--types] [: type]
                   every name with its type, sorted; the prelude hidden unless a filter or --all;
                   a glob (* anywhere, else a substring), a kind, or a type query whose lowercase
                   unknown names are variables, matched by unification both ways
:type e            inferred type scheme of e
:hash name         current ref of name
:names #hash       every name that points at the hash (current or historical)
:history name      refs the name has pointed at, newest first
:view name         pretty-print the term with refs rendered as in 7.2; for a type, its declaration
:core name         print the Typed Core (5.3) with every annotation
:lint name         re-run lint on a stored definition and print its type(s)
:dependents name   definitions whose terms reference the current ref of name
:alias new old     point new at old's current ref
:unname name       remove the label (of a definition, a type or a constructor; .f for a field); the term stays

Session
:set precision n   significant digits printed; working precision is n + 4 (3.2.8)
:set sigma k       confidence multiplier for comparisons on statistical values (3.2.9)
:prefer [unit]     print values of the unit's dimension in it (3.2.12); alone, list preferences
:unprefer unit     remove that preference
:set unicode on    pretty-print with unicode spellings (2.8); off (the default) for ASCII
:set               list the settings: precision, sigma, unicode
:exact e           raw rational, or midpoint and nudge list
:budget e          error budget (3.2.6)
:covariance e      covariance (or variance) of the statistical nudges, and the bound box (3.5)
:load file         enter a file into the scratch as one binding group
:colour [on|off]   colour the REPL's output; alone, say whether it is on (a REPL-level setting, below)
:quit
```

With `:set unicode on`, printed values, `:type`, `:view`, `:edit`, `:exact`,
`:budget`, `:covariance` and the `:prefer` message use these spellings from
the table in §2.8, and nothing else changes except the echo described below:

| ASCII | Unicode | Where |
|---|---|---|
| `^2` `^-1` | `²` `⁻¹` | unit exponents (`9.81 m s⁻²`, `5 km h⁻¹`), dimension brackets in types (`Num [m s⁻²]`), powers in `:view` (`x²`) |
| `->` | `→` | function types, lambdas and case alternatives |
| `\` | `λ` | lambdas: `λx → x² + 1` |
| `<=` `>=` `/=` `\|\|` | `≤` `≥` `≠` `∨` | operators in `:view` |

`*` stays `*`, because `×` is the cross product; `/`, `&&`, `sqrt` and names
such as `pi` and `deg` keep their ASCII spelling. `√` would change the
binding (it is a prefix operator, `sqrt` an application), and `π` and `°`
are names, not syntax. `·`, `∧`, `⊙`, `⊘`, `±` and `±σ` print in unicode
in both modes, as before. A power whose base does not end in an atom keeps
its caret, since a superscript must be glued to an atom. Every unicode form
lexes to the same tokens as its ASCII form, a superscript standing for its
caret, so output reads back either way. Error messages, `:core` and `:lint`
stay in ASCII.

**The echo.** With `:set unicode on`, a statement line (not a `:` command)
that has a unicode spelling is first echoed in it, on a note line of its own
that starts `  ≡ `: `2 +-s 0.1` prints `  ≡ 2 ±σ 0.1`, then its value. The
echo re-spells the tokens as they were typed, at their spans, and keeps every
other character, spacing and comments included. `+-s` `+-` `->` `\` `<=`
`>=` `/=` `||` `@` `><` `/\` `.*` `./` and the composition `.` become `±σ`
`±` `→` `λ` `≤` `≥` `≠` `∨` `·` `×` `∧` `⊙` `⊘` `∘`, and a caret power with
an integer literal exponent, glued to an atom, becomes a superscript (`x^-1`
is `x⁻¹`; `x ^ 2` keeps its caret). Names keep their spelling (`sqrt`, `pi`,
`deg`), and so do `*`, `/` and `&&`, for the reasons above. The echo lexes
to the same tokens as the line. A line with nothing to re-spell, a line that
fails, and a file read by `:load` are not echoed. The echo is a note to the
reader, not output, and the REPL may print it dim.

**The last result.** After an expression statement evaluates, `it` names that
expression for later expressions and for the inspection commands: `1 + 2`
then `it * 2` prints `6`, `:type it` gives its type, `:view it` prints `it =
1 + 2`, and `:exact`, `:budget`, `:covariance`, `:core`, `:hash` and `:lint`
take it as they take a definition. On a line with several expressions, each
one is `it` for the next. `it` is the expression, not its printed value: it is
hashed as a definition is, so a `±` in it is the same nudge every time it is
used, and `:exact it` labels that nudge `it`. An input that fails leaves the
previous `it`; before the first expression, `it` is an unknown name. `it` is
local to the session (§7.5): `:ls`, `:edit`, `:alias` and `:dependents` do
not see it.
#### The REPL

The interactive REPL adds editing aids on top of the commands. None of them
changes what an input means or the text it prints.

**Completion.** TAB completes the word before the cursor:

- at the start of a line, a `:` command;
- after `:set`, the setting; after `:set unicode` and `:colour`, `on` or `off`;
- after `:load`, a file name;
- after a `.` glued to a value, a record field name (`b.ma` gives `b.mass`);
- elsewhere, a name the session sees (definitions, units, types and
  constructors, pending ones included) or a keyword.

The prelude has many hundreds of names, so a short prefix can list many
candidates.

**Unicode by name.** A backslash, a name, then TAB enters a character, as
in Julia: `\mu` gives `μ`. When the typed name is a whole entry, it is
replaced, so `\pm` gives `±` although `\pms` exists. Otherwise TAB lists
the entries that start with it. The table is in `Eval.Unicode`:

| Names | Result |
|---|---|
| `\alpha` … `\omega` (`\lambda` is the lambda `λ`, `\pi` is `π`) | Greek letters |
| `\Gamma` `\Delta` `\Theta` `\Lambda` `\Xi` `\Pi` `\Sigma` `\Upsilon` `\Phi` `\Psi` `\Omega` | the capitals that do not look like Latin ones |
| `\micro` `\ohm` | `μ` `Ω`, the forms the lexer folds `µ` and `Ω` to |
| `\to` `\otimes` `\cdot` `\times` `\odot` `\oslash` `\div` | `→` `⊗` `·` `×` `⊙` `⊘` `÷` |
| `\le` `\ge` `\ne` `\or` `\neg` `\wedge` `\star` `\circ` `\sqrt` | `≤` `≥` `≠` `∨` `¬` `∧` `⋆` `∘` `√` |
| `\pm` `\pms` | `±` `±σ` |
| `\deg` `\degC` `\degF` `\prime` `\dprime` | `°` `°C` `°F` `′` `″` |
| `\^0` … `\^9` `\^-` | `⁰` … `⁹` `⁻` |
| `\_0` … `\_9` | `₀` … `₉`, inside identifiers |

`\leq`, `\geq`, `\neq`, `\vee`, `\lnot`, `\rightarrow` and `\pprime` are
aliases. There is no `\and`: `∧` is the wedge product, and boolean and is
`&&` only (§2.8). Every entry lexes to the same tokens as its ASCII
spelling in §2.8, or is a letter that is valid in an identifier. Two kinds
of entry have tokens of their own: a superscript and `√`. For these, the
value must equal that of the caret power or of `sqrt`. The test suite
checks all of this against the lexer.

A word that starts with `\` completes from this table only, never from
names. Nobody presses TAB in a lambda such as `\x -> x`, so the two uses
never meet; TAB after `\x` would offer `\xi`.

**Colour.** The REPL colours its output when stdout is a terminal, `TERM`
is not `dumb` and `NO_COLOR` is not set:

- In an error, the `error at` line and the message are red and the carets
  bold red. The source excerpt stays plain.
- Notes are dim: `pending:`, `added`, `updated`, `left`, `nothing to …`,
  the hidden-prelude line of `:ls` and the like.
- In a `name : type` line of `:ls`, the type is dim.
- In a value, the trailing unit is dim (`12.566… m^2`, `[1, 2, 3] km s⁻¹`).
- The prompts, `> ` and the continuation prompt `… `, are bold.

`:colour on` and `:colour off` override the default. This is a setting of
the REPL, not of the session: `:set` does not list it, and the one-shot and
file modes never colour. The text is the same with colour or without.

**Continuation lines.** An input can span several lines. After each line
the REPL decides whether the input is finished. If it is not, the REPL
reads another line at the prompt `… ` and appends it after a newline. The
input goes on when:

- a `(`, `[` or `{` is not closed;
- its last token cannot end an input: `=`, `->`, `\`, `|`, `,`, `;`, a
  backtick, `√`, an infix operator (`+ - * / ^ == /= < <= > >= && || : .
  ∘` and the others of §2.5), `±` or `±σ`, or a keyword other than `true`
  and `false` (`of`, `where`, `in`, `then`, `else` and the rest);
- a line ends in `of` or `where`. The entries of that block follow on
  indented lines, and the input goes on until a blank line.

The decision reads the lexer's tokens, so a comment never counts: `x -- (`
is finished, and so is `1 + 2 --`. A field access glued to a value
(`b.mass`) is one token and ends an input. A `.` with nothing after it is
composition, so it does not. A `:` command never goes on. Text that does
not lex is fed as it stands, so the lexer's error shows.

A blank line at the continuation prompt ends the input as it stands. The
input is then fed, and an unfinished one gives the parser's error as usual.
Ctrl-C or Ctrl-D at the continuation prompt abandons the input and prints
`(input abandoned)`. At the `> ` prompt they end the session, as before.

A continuation line keeps its indentation, and the layout rule (§2.2) reads
the input as it reads a file. A line indented further than the first line
continues its statement; a line at the first line's column starts a new
statement in the same binding group.

```
> data Shape = Circle (Num [m]) | Rect (Num [m]) (Num [m])
> let area s = case s of
…   Circle r -> pi * r^2
…   Rect w h -> w * h
…
> let f x =
…   x + 1
> f 2
3
```

An input ends at the first line that leaves it finished, unless a block is
open. So a later line that starts with `where` or `else` is not joined to a
finished line before it: `let f x = y * 2` is fed before `  where y = x + 1`
is read. Put the `where` at the end of the first line, or use `:load`.

`eval -i` reads continuation lines in the same way, so a piped script can
hold multi-line definitions. Each line is echoed after the prompt it was
read at, `> ` or `… `.

**History.** The line history is the file `history` in the codebase
directory (§7.4). With `--no-codebase` there is no history file. Each
physical line is one entry, so a multi-line input is recalled line by line.
haskeline writes its history file one entry per line, and its line editor
does not redraw an entry that contains a newline, so the lines are not
joined into one entry.

### 7.4 CLI and persistence

```
eval                     REPL
eval 'expr'              one-shot: print the value, exit 0; on error print to stderr, exit 1
eval -f file.ev          load a file as a binding group, print bare expressions
echo 'expr' | eval       same as -f on stdin
eval --codebase DIR …    use an explicit store
eval --merge OTHER       merge the store at OTHER into this one, leaving OTHER as it was
```

A codebase on disk is a directory:

```
format             "eval codebase 3": the storage format version
terms/<hex hash>   one term per file: the canonical encoding of 6.1 with each
                   binder's name hint after its tag and each reference's written
                   name after it, so :view keeps the author's names and units are
                   decided by the name used; the hash is recomputed on load
types/<hex hash>   one declared type per file, in the encoding of 6.1; loaded
                   before the terms, which may mention them
names.log          append-only, one event per line:
                     <unix time> bind <name> <hex hash>[.<i>]
                     <unix time> unname <name>
                     <unix time> unit <name>
                     <unix time> scale <name>
                     <unix time> prefer <unit text>
                     <unix time> unprefer <unit text>
                     <unix time> type <name> <hex hash>          -- a type label
                     <unix time> con <name> <hex hash>.<i>       -- a constructor label
                     <unix time> field <name> <hex hash>.<i>.<j>  -- a record field label
history            the REPL's line history
```

Types and Typed Core are not stored; they are recomputed on load by
typechecking and linting each term, dependencies first (cheap: the prelude's
700 definitions take 30 ms). Terms are only ever added, so two stores never
conflict on terms; the log is the one thing with order, and merging two stores
is concatenating their logs and sorting by time, last writer winning per name.

`eval [--codebase DIR] --merge OTHER` does that, into the store that `eval`
would otherwise use. Both stores are opened as usual, so an older format is
migrated in place, OTHER included, and the summary says so; a directory that is
not a store is refused and left untouched. Every file in OTHER's `terms/` and
`types/` that DIR lacks is copied after its hash is checked as on load; a file
that is already there is the same content and is never overwritten, and a
corrupt one is skipped with a note. Then OTHER's log lines that DIR does not
already have are added, and the whole log is stably sorted by its leading time
and written through a temporary file, after the terms, so an interrupted merge
never leaves a name pointing at a missing term. On equal times DIR's line comes
first and OTHER's wins. A line with no readable time sorts as if at time 0 and
is reported. Merging again adds nothing. The `history` file is DIR's own and is
neither copied nor touched. The summary gives the terms, types and log lines
brought across, then the notes.

The user store lives at `$XDG_DATA_HOME/eval/` and is what the daily calculator
uses. A project-local `.eval/` directory, found by walking up from the current
directory, shadows the user store, and `--codebase DIR` names one explicitly;
`--no-codebase` runs in memory. iapetus commits its `.eval/` to git.

The prelude is entered at the start of every session as an ordinary binding
group, in memory, and the store's log is replayed on top of it. Prelude
*bindings* are therefore never written: a user who rebinds `c` keeps that
binding across sessions, and a prelude that changes `G` rebinds `G` on the next
start while the user's dependents keep pointing at the old hash, which `:todo`
reports as stale. Prelude *terms* that a stored definition references are
written beside it, so a store stays self-contained whatever the prelude later
becomes. Each successful input is written through immediately: new terms first,
dependencies before dependents, then the log lines, so an interrupted session
never leaves a name pointing at a missing term. A term that fails to decode,
fails to typecheck, or is named but missing is reported as a note at start and
skipped; the rest loads.

Format 1 stores (no written names after references, unit flags on
references) are migrated in place on first open: every term file is decoded by
the old rules and rewritten, with empty hints, and old `unit <hash>` lines in
the log flag every name then bound to that hash. Hashes do not change, so the
log and the names stay valid.


Format 2 stores are migrated to 3 on first open as well, and this one changes
hashes: `If` and the boolean literal became `Case` and `Con`, so every term that
used them is decoded by the format-2 rules, re-encoded, and re-hashed, and the
references to it and the `bind` lines of the log are rewritten to the new hash in
dependency order. Old term files are removed.
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
- **`it`**, the last expression (§7.3), is never stored. It is not in the
  scratch, so `:add` and `:update` do not see it, and nothing reaches the
  codebase or the store through it. A definition that mentions it is refused
  with "`it` is the last result and cannot be stored; paste its definition
  (:view it) instead", and so is a definition named `it`. `it` keeps the
  terms it was checked against, so replacing or forgetting a pending
  definition it used does not break it.

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
  laziness supplies thunks, which `case` and recursion rely on.
- `Con` builds a data value whose fields are thunks; `Case` forces its scrutinee
  to a constructor and binds the fields, unevaluated, in the chosen alternative.
  Booleans are the two nullary constructors; lists are cons cells of thunks, so
  an infinite `range` is fine until something walks it.
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
   Status: done. `unit` declarations, the generated prelude, display units
   through products and sums, and `to`.
3. **Affine magnitudes.** `Eval.Affine` (magnitudes, rigorous elementary
   functions on rationals, lifting by linearisation), all transcendental
   builtins, hash-named nudges with kinds, `±`, `±σ`, `noise` and `gauss` with
   definition-site identity, compaction and slack, certain-digit printing,
   `:exact`, `:budget`, `:set precision/sigma`, CODATA `G` and the derived masses in
   the prelude. Status: done. Remaining from this item: precision refinement
   for undecidable comparisons (item 8) and `e` as a constant (left out for now:
   `e` is the eccentricity in most orbital code).
4. **Tensors.** Shape-indexed types, the product operators and their shape
   constraints, literals and printing: done. Remaining: `norm`, `inverse`,
   `det` kernels: done (Gaussian elimination with pivots whose enclosure
   excludes zero), `covariance`, `cholesky`, `:covariance`, `±` and `±σ` on
   tensors and `v ±σ P` (§3.4, §3.5): done. `contract` and `permute` with
   literal positions at any rank, and the prelude's `trace` (§3.3, §4.2):
   done. Slicing along any axis, `t._.i` and `slice k i t` (§2.10): done.
   Remaining: mixed-dimension matrices for a joint state covariance.
   Points and scales (§3.6): done, over any shape; frames with a rotated
   basis remain.
5. **Mutual recursion.** SCC analysis, cycle hashing, group inference.
6. **Persistence and REPL polish.** User and project-local stores, haskeline, all
   `:` commands, error messages with source spans. Status: stores done (§7.4),
   haskeline with a history file beside the store, `:store`, `:prefer`,
   `:covariance`, `:set unicode` (§7.3), and `eval --merge OTHER` to merge two
   stores (§7.4). Nothing remains here.
7. **Tuples**, then **lists** with a `case` construct in the core. Status: done.
   `Con` and `Case` replaced `If` and the boolean literal (core.md §5). User
   data types (§2.3): done, as the same mechanism with declared constructors,
   kinded parameters inferred from use, self-recursion, owner-stamped or
   structural identity, and persistence in `types/`. Records: done, as field
   labels on one-constructor types with `b.f`, `C {f = e}` and `b {f = e}`
   desugaring to `case`; record values print with their field names.
   Remaining: `==` on declared types, mutually recursive types, and
   re-expressing `Bool`, tuples and lists as prelude declarations.
8. **Later.** Named projection positions as a scoped sugar (`.x .y .z`,
   `.pos .vel`, §2.10); precision refinement for undecidable comparisons
   (re-evaluate at higher `p`); type annotations; mixed-dimension matrices, which
   unlocks joint state covariance as a value; ball-plus-zonotope enclosures for
   radial bounds; non-SI and affine-offset units (°C); rewrite rules that
   fuse `star (wedge a b)` back into a hand-coded 3D cross kernel and notice
   when only part of a product is consumed (laziness already avoids the
   arithmetic, not the allocation); compilation for long
   propagations.

9. **Design first, then delegate.** Each of these needs a decision written
   down before any code; once it is, the implementation is routine enough to
   hand off.
   - *Mixed-dimension matrices.* What a matrix with a dimension per row and
     per column is, how such types unify, and what `*` and `inverse` mean on
     them. This is what a joint position-velocity covariance needs (§3.5).
   - *Frames with a rotated basis.* The semantics of a scale over a tensor
     with a rotation as well as an origin (§3.6): what `to` does, how
     displacements and covariances transform.
   - *Precision refinement for undecidable comparisons.* Re-entering
     evaluation at a higher precision cuts across the evaluator's
     architecture (§3.2.9).
   - *Anything hash-changing.* Re-expressing `Bool`, tuples and lists as
     prelude declarations, or mutually recursive types. Each is a numbered
     migration (core.md §6); a mistake there corrupts stores.
   - *Type annotations.* The parser and inference interplay, and what the
     error messages say when an annotation and the inferred type disagree
     (§4.6).
   - *A brick front end*, `eval --tui`, beside the line REPL: the canonical
     echo live as you type, completion as a popup, multi-line editing, and
     room for panes (a `:ls` sidebar, the error excerpt beside the input).
     Built on the same `Eval.Repl` logic so the two never drift; the line
     REPL stays the default and the only front end for piped scripts and
     tests. `brick` and `vty` come in through `build-depends` via
     `callCabal2nix`.

---

## 11. Open questions

- Comparison operators beyond the certain `<` and `==` (§3.2.9): possible
  comparisons `<?` and `=?` ("consistent with", at `k` sigma for statistical
  nudges), tolerance equality `a ≈ b within t`, and enclosure containment. The
  accessors `mid`, `bound`, `sd` that let a user write any policy exist
  (§3.2.9), so each of these can be tried as a prelude definition before it
  earns an operator. A three-valued boolean that flows into `if` is ruled out.
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
- Equality on declared types is derived structurally when every field is
  comparable (§4.2), the rule tuples and lists follow. Still open: whether a
  type may opt out, or give its own equality (a fraction kept as an
  unreduced pair, which structural equality calls unequal to its reduced
  form).
- `==` on data evaluates every field even after one is unequal, so `Pair 1 (2 ± 0.1) == Pair 2 2` says "cannot decide" where false was knowable; tensors, tuples and lists do the same. Short-circuit, or keep the uniform rule?
- A constructor that takes a prelude unit's name (`data Temp = T …`) unnames
  the tesla silently. Warn, refuse, or keep the newer-label rule?

---

## 12. Worked scenario: iapetus

An illustrative session with `:set precision 6` for brevity. Numbers are rounded for
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
[0.000000…, 1.000000…, 0] km            -- radii ~1e-10, below the last printed digit
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

# Design: `metron`

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
`metron '5 km/h to m/s'` into every day. It must give exact answers, handle units
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
- Interactive use (REPL) and one-shot use (`metron 'expr'`) from day one.

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
- **Historical references**: glued `name#hash` or bare `#hash`, optionally
  followed by a glued `.index` for a recursive-group member. Hash prefixes
  use lowercase base32hex (`0-9`, `a-v`) and must identify a unique reference.
  A bare hash in an application argument or quantity suffix needs parentheses,
  as in `f (#hash)`, so trailing measurement labels remain unambiguous.
- **Keywords**: `let`, `in`, `where`, `if`, `then`, `else`, `to`, `true`, `false`,
  `unit`, `chart`, `space`, `on`, `from`, `at`, `case`, `of`, `data`,
  `namespace`, `use`, `forall` (also `∀`). (`as` in
  `use a as k` is not a keyword: it is also the attosecond.)
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
display unit (§3.2.12), `chart name params… on parent [at origin] [step unit] [by B [then B …]] [spinning ω]` a chart
(§3.6, §3.8). A `data`
declaration (§2.3) proposes a type the same way. `:add` and `:update` move
scratch definitions into the codebase (§7).
Within one input a name may be defined only once, as in a Haskell module; across
REPL inputs a pending definition is replaced by a newer one.

`name :: type`, on a line of its own, is a **signature** (§4.8): it gives
the definition of that name in the same input, before or after it, a type
to be checked against, written as `:type` prints types (§2.3). It is a
statement like the others, so it may stand in a `namespace` block, where
it signs the block's definition of that name. A signature with no
definition in the input, the scratch or the codebase is an error.

```
area :: Shape -> Num (m^2)
let area s = case s of Circle r -> pi * r^2; Rect w h -> w * h
```

`namespace a.b` followed by an indented block of statements puts what the
block declares under the path `a.b` (§7.6); blocks nest. `use a.b` and
`use a.b as k` make the names of a namespace resolve bare, or under the
prefix `k.`, for the statements after it in its block, and a top-level
`use` lasts for the rest of the REPL session (a file read with `:load` keeps
its `use`s to itself). The statements of a `namespace` block and the `use`
form are part of the input's binding group like any other.

```
namespace orbital
  let mu = 398600.4418 km^3/s^2
  let period a = 2 * pi * sqrt (a^3 / mu)    -- mu is orbital.mu
use orbital
period (7000 km)
```

Layout is deliberately simpler than Haskell's: a token that starts a line at the
column of its enclosing context starts a new statement (or `where` binding), a
token further right continues the previous one, and there is no parse-error rule.
So a multi-line `let … in` expression must indent the `in`, and a bracket that
spans lines must indent its continuation lines. A `namespace` block opens at
the first token after its path, as a `where` block does at the first token
after `where`, and that token must be indented further than the `namespace`
line; a block with nothing indented under it is an error, so a forgotten
indent cannot silently put the rest of a file into the namespace.

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

`Bool`, tuples and lists are not built into the language: they are three
`structural data` declarations (below) that the compiler holds as values and
refers to by hash, which the declarations alone fix:

```
structural data Bool = False | True
structural data Pair a b = Pair a b
structural data List a = Nil | Cons a (List a)
```

`true`, `if`, `(a, b)`, `{a, b}` and `x : xs` are syntax for their
constructors and `case`, and print back as written whatever names the types.
A tuple of `k` components is the structural type of one constructor with `k`
fields, `Pair` the case `k = 2`; a tuple has at most 32 components, so that
its type is known from its hash. The standard library names the three under
`std` (§7.7), so `True`, `Pair 1 2` and `Cons 1 Nil` are `true`, `(1, 2)` and
`{1}`, and `:view std.List` prints the declaration; renaming or unnaming them
changes only how a name prints. A user's `structural data Bool = False | True`
is the same type; `Bool` is otherwise reserved.
Since a structural type is its shape, any `structural data` of that shape
is one of these: `structural data Color = Red | Green` is `Bool` (`Red`
prints `false`), and a structural type of one constructor whose fields are
its parameters in order, `structural data P a b = P a b` or a record
`structural data R a b = R {x :: a, y :: b}`, is a tuple and prints as one.
A nominal `data` declaration is never one of them.

**Declared data types.** A `data` statement declares a type as a sum of
products, as in Haskell, with parameters of any kind:

```
data Shape = Circle (Num m) | Rect (Num m) (Num m)
data Maybe a = Nothing | Just a
data Tree a = Leaf | Node (Tree a) a (Tree a)           -- recursion through the type itself
data State n = State (Vec n m) (Vec n (m/s))            -- n is a length, from its use
data Reading d = Reading (Num d) (Point degC)           -- d is a dimension; a point on a frame (3.10)
structural data Pair a b = Pair a b
```

A field is a type atom: a name (`Bool`, `Num`, a parameter, a declared type
of no parameters) or a compound type in parentheses, written as `:type` prints
it: `Num m`, `Vec 3 (m/s^2)`, `Mat 3 3`, `Tensor [2, 3] d`, `Point degC`,
`Chart lvlh`, `Diff lvlh`, `(a, b)`, `{a}`, `a -> b`, `Maybe (Num m)`. A length may
also be `rank s` for a shape parameter `s` (§4.1): `data Idx s = Idx (Vec (rank
s))`. `rank` is the one type-level function and cannot name a parameter. A
dimension is a type argument (§4.1): one name bare (`Num m`, `Num N`, `Num
d`), anything else in parentheses (`Num (m/s^2)`, `Num (km/h)`). Its names
are base units (`m kg s A K mol cd rad`), declared units, which mean their
dimension, and parameters, joined with `*` or `·` and `/`, with `^` or
superscript exponents, parentheses and `1`; square brackets are only ever a
shape. A parameter's kind is read off the positions it appears in, so it
needs no annotation; using one both as a dimension and as a type is an
error.

Constructors are functions and values: `Circle` has type `Num m -> Shape`,
`Nothing` type `Maybe a`, and `map Just xs` works. Arguments are plain
application: `Rect (3 m) (4 m)` passes two quantities, while `Rect 3 m 4 m`
would pass four arguments, the metre twice among them (§2.6). A
`case` takes a value apart one constructor deep, naming the fields in order;
`_` and variables fill in the constructors not written, as for lists. Values
print with each compound field in parentheses, `Rect (3 m) (4 m)` and
`Just (Circle (1 m))`, so that they read back whatever their units; a
record prints with its field names (below).

A type's identity is its definition: parameter kinds, the constructors' field
types in order, and the type's full path as an owner stamp (§3.2.4), so two users
who declare `data Shape = …` alike share one type and `data Blob = Circle (Num
m)` is another. `structural data` leaves the name out, so any two structural
declarations of the same shape are the same type. Constructor names and the
type name are labels in the codebase, like definition names (§7): `:unname
Circle` leaves the constructor printing as `#a3f9k.0`, `:view Shape` prints
the declaration back, and a constructor name and a definition name share one
namespace, the newer label winning (declaring `data Temp = T (Num K)` in
`namespace si` would unname the tesla `si.T`; at the root it only
shadows it, as any root name shadows the library's, §7.7). A declaration is
pending in the scratch (§7.5) until `:add`, like a definition. `==` and `/=`
work on a declared type when every field of every constructor has equality
(§4.2), as on tuples and lists: `Circle (1 m) == Circle (1 m)` is true, values
built by different constructors are unequal, and a type with a function field
has no equality.

**Records.** A constructor may name its fields, which makes the type a record:

```
data Body = Body {mass :: Num kg, pos :: Vec 3 m, vel :: Vec 3 (m/s)}
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
(3 m :: Num m)                     -- an ascription: narrows the type (§4.8)
```

### 2.4 Vector and matrix literals

```
[1, 2, 3]                       -- Vec 3
[1, 0; 0, 1]                    -- Mat 2 2, rows separated by ;
[[1, 0], [0, 1]]                -- the same matrix, nested
[1; 2]                          -- Mat 2 1, a column
[1, 2; 3, 4;; 5, 6; 7, 8]       -- Tensor [2, 2, 2]: ;; separates planes
[x, y, z] m                     -- Vec 3 m, via the quantity rule
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
| 1 | `to`, `from … to`, `on` | left, through `to` | conversion (a unit, a point to a chart, an amount along a chart's axes; `from` names a configuration) and subtraction in a frame, `b .- a on c` (§3.10, F7, F10); lowest so `5 km / h to m/s` reads naturally. Any of them may be followed by more `to`s, which chain from the left: `x to a to b` is `(x to a) to b`, and `v from c to c1 to km/s` converts, then displays |

`#label` is not an operator but a postfix on a `±`, `noise` or `gauss`
expression (§3.2.4). It is parsed after level 5 and before level 4, so it
attaches to the whole `±` expression and `x == 5 ± 0.1 #s7` labels the `±`,
not the comparison.

`+ - * /` are overloaded; everything else that works on vectors or matrices is a
named function: `dot`, `cross`, `norm`, `transpose`, `inverse`, `det`,
`vmap`, `noise`, `gauss`, `covariance`, `cholesky`. Component access is the postfix
projection `v.0`, `m.1.2` (§2.10), never a function taking a computed index.

### 2.6 The quantity rule

A number or vector literal followed by one or more atoms is a **quantity**
(built as §3.10, U4 and U5, decide):

```
quantity ::= number unitatom+
           | vector unitatom+
unitatom ::= atom [ '^' [ '-' ] natural ]
```

Declared unit syntax after a literal (§3.10) makes the amount `scale lit u : Tensor σ δ`; a chart makes the point
`pointOn c lit` (§3.6); anything else is refused, "`pi` is a Num, not a unit or
a chart: write the `*`". Juxtaposed atoms multiply, `9.81 m s^-2` being
`9.81 (m*s^-2)`. Two literals side by side, `5 4 3` or `2 [1, 2]`, are a
parse error. The rule exists for units, not arithmetic: `5 * 4 * 3` and `5
* a` are clearer written out. The whole quantity binds like an application.

**Unit operators bind before numbers.** After a literal the quantity takes
the whole unit expression: in a chain of `*` and `/` it takes in each
following factor that is a declared unit's name (§3.2.12, a base unit or a
name declared with `unit`), with or without a power. A number ends it, and so
does any other name. The parser leaves the chain as it is and the desugarer,
which knows which names are declared units, regroups it; names decide only
the grouping, and the types decide what each operator means (U2).

| Written | Means |
|---|---|
| `3 m` | `scale 3 m` |
| `3 m^2 kg` | `3 (m^2*kg)` |
| `9.81 m/s^2` | `9.81 (m/s^2)` |
| `5 km/h` | `5 (km/h)` |
| `9.81 m s^-2` | `9.81 (m*s^-2)`, as values print, so they read back |
| `[1, 0, 0] km` | `scale [1, 0, 0] km` |
| `3 (m/s)` | `3 (m/s)` |
| `6 m / 2 s` | `(6 m) / (2 s)`: a number ends the quantity |
| `6 m / x` | `(6 m) / x`: `x` is not a declared unit |
| `x / 1 km/h` | `x / (1 (km/h))` |
| `20 degC` | `pointOn degC 20` |
| `5 a`, `2 pi`, `3 f x` | errors: not units or charts |

A unit name is syntax, not an ordinary value (§3.10). At an operand of
`*` or `/`, a unit expression means one of that unit: `x * km` is
`x * (1 km)`. Other value positions require an explicit amount. An
expression after a coordinate literal that is not declared unit syntax
must be a chart; `\c -> 3 c` infers a chart over a scalar space. Core
holds `scale` or `pointOn`, never the surface quantity rule.

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
             | 'chart' name param* 'on' expr clause*       -- a chart (3.6, 3.8, 3.10 F10); with parameters a moving chart
             | 'space' name '=' type                      -- a space: Num δ or Vec n δ (3.10 F2)
             | ['structural'] 'data' name param* '=' con ( '|' con )*   -- a data type (2.3)
             | 'namespace' path statements                -- an indented block (7.6)
             | 'use' [ '.' ] path [ 'as' name ]            -- 'as' is a name, not a keyword (7.6)
             | name '::' sigtype                          -- a signature (4.8)
             | expr
clause     ::= 'at' expr | 'step' expr | 'by' expr ( 'then' expr )* | 'spinning' expr
                                                       -- in any order, each once, each running to the next clause word outside brackets;
                                                       -- 'step', 'by' and 'spinning' are words here only; 'then' separates generators
                                                       -- applied in order, an 'if' keeping its own
path       ::= name ( '.' name )*                       -- glued dots
statements ::= statement ( sep statement )*            -- indented block, opened as after 'where'
qname      ::= [ '.' ] name ( '.' name )*              -- a qualified or absolute name (7.6)
con        ::= name tyatom* | name '{' name '::' type ( ',' name '::' type )* '}'   -- a record (2.3)
sigtype    ::= [ 'forall' binder+ '.' ] type               -- a signature's or an ascription's type (4.8): its variables
binder     ::= name | '(' name ':' natural ')' | '(' name ':' qname ')'   -- a variable, one sized: that many axes of its own (3.9), or a frame of a space (3.10 F1)
type       ::= tyapp [ '->' type ]
tyapp      ::= qname tyatom* | tyatom
tyatom     ::= qname | natural | '(' type ( ',' type )* ')' | '(' dim ')' | '{' type '}' | '[' shape ']'
shape      ::= [ length ( ',' length )* ]                -- a shape: [2, 3], [n, lvlh]; brackets hold nothing else
length     ::= qname | natural
dim        ::= type power ( dimop factor )* | type ( dimop factor )+   -- a dimension (4.1): (kg*m^2/s^2), (m²/(s²·K)), (1/s)
dimop      ::= '*' | '·' | '/'                            -- one precedence, to the left: m/s*kg is m·kg/s; '@' is refused
factor     ::= ( qname | natural | '(' type ')' | '(' dim ')' ) [ power ]
power      ::= '^' [ '-' ] natural | superscript
bindings   ::= binding ( sep binding )*            -- indented block
binding    ::= name param* '=' expr
param      ::= name
expr       ::= 'let' name param* '=' expr 'in' expr
             | '\' param+ '->' expr
             | 'if' expr 'then' expr 'else' expr
             | binary [ conversion ( 'to' binary )* ]   -- level 1 of 2.5: further 'to's chain from the left
conversion ::= 'to' binary | 'from' binary 'to' binary | 'on' binary
binary     ::= operator-precedence parse over 'unary' using the table in 2.5,
               with `name` as an infix operator at level 9, and
               '#'label as a postfix just below ± (§3.2.4)
unary      ::= '-' unary | 'sqrt' unary | power
power      ::= app [ '^' [ '-' ] natural ]
app        ::= quantity | atom argument*
argument   ::= atom                                      -- not an unparenthesised bare #hash
quantity   ::= number unitatom+ | vector unitatom+          -- the desugarer regroups a * and / chain after it (2.6)
unitatom   ::= argument [ '^' [ '-' ] natural ]
atom       ::= primary postfix*
postfix    ::= '.' projection | '.' name                -- glued: a component, or a record field (2.10)
             | ( '._' )+ '.' projection                -- glued: a slice along axis k = the number of '._' (2.10)
             | '{' name '=' expr ( ',' name '=' expr )* '}'    -- record construction or update (2.3)
projection ::= natural
primary    ::= number | name | '.' name | 'true' | 'false'     -- '.' name not glued: absolute (7.6)
             | hashref
             | '(' expr ')' | section | vector | matrix
             | '(' expr ( ',' expr )+ ')'                      -- a tuple
             | '(' expr '::' sigtype ')'                       -- an ascription (4.8)
             | '{' [ expr ( ',' expr )* ] '}'                   -- a list
             | 'case' expr 'of' alts                       -- alts: an indented block, or ; separated
hashref    ::= [ qualified-name ] '#' hashprefix [ '.' natural ] -- glued when named
hashprefix ::= ( '0'..'9' | 'a'..'v' )+
alt        ::= pattern '->' expr
pattern    ::= '(' name ( ',' name )+ ')' | '{}' | name ':' name | 'true' | 'false' | '_' | name name*
             | qname name*                        -- a qualified or absolute constructor (7.6)
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
| `·` `⋅` | `@` | contracting product: dot, matrix-vector, matrix-matrix; name `dot`. In a dimension (§4.1) `·` is `*`, the product, and `@` is refused |
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
| `∀` | `forall` | binds a signature's or an ascription's type variables (§4.8); input only, printed `forall` |
| `²` `³` `⁻¹` … | `^2` `^3` `^-1` | superscript digits and `⁻` as a power: `m/s²`, `s⁻²` |
| `π` | `pi` | the constant |
| `°` | `deg` | postfix unit: `45°` is `45 deg` |
| `″` `′` | `arcsec` `arcmin` | postfix units |
| `₀` `₁` … | `_0` `_1` … | subscripts inside identifiers only |

Rules: superscripts bind as `^` does, so `3 m²` is `3 (m^2)` by the quantity rule.
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
| `3 m²`, `3 m s⁻²` | `3 (m^2)`, `3 (m*s^-2)` (quantity rule) |
| `45°` | `45 deg` |
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

**Qualified and absolute names** (§7.6). A dot and a name that are *not*
glued to an atom start one: `.km` is an absolute name, the root's `km`
whatever namespace is current or `use`d, and `.orbital.period` the full path
from the root (so `f .g`, once an error, is `f` applied to the root's `g`).
A glued chain on a name, `orbital.period` or `o.period`, lexes as field
accesses, and the desugarer decides: when the name at its head is not a
local binder, the longest dotted prefix of the chain that resolves (§7.6) to
a definition or a constructor is a qualified reference, and the fields
after it are field accesses. `orbital.earth.mass` is the field `mass` of the
definition `orbital.earth`; `b.mass`, with `b` a lambda parameter, is a
field access whatever labels exist. The one ambiguous case, a value
`orbital` with a field `period` beside a definition `orbital.period`, cannot
arise, because a name is never both a label and a namespace (§7.6). A field
written after the dot is a bare name resolved through the scope; a record
built with a constructor (`orbital.Body {mass = …}`) takes the field names
as that constructor's own, wherever the type lives.

---

## 3. Values, numbers and units

### 3.1 The value universe

| Static type | Runtime value | Notes |
|---|---|---|
| `Num δ` | a magnitude (§3.2) plus a dimension vector and a display-unit hint | `δ` is checked statically; the runtime dimension vector exists only for printing. `Num δ` is the rank-zero tensor `Tensor [] δ` (§3.3) |
| `Bool` | `true` or `false`: constructor `False` or `True`, no fields | `structural data Bool = False \| True` (§2.3); `if` is `case` on it |
| `(a, b, …)` | a tuple of values: the one constructor, its fields as thunks | the structural tuple type of its arity, `Pair a b` for two; components of any types, so a state `(r, v)` has two dimensions |
| `{a}` | a list: `{}` or `x : xs`, constructor `Nil` or `Cons` | `structural data List a`; the one unbounded structure; lazy, so `range` and `map` stream |
| `T α…` (declared, §2.3) | a constructor and its fields, as thunks | `Shape`, `Maybe (Num m)`, `Tree a`; `Bool`, tuples and lists are three of them |
| `a -> b` | a closure: core term plus environment | first class; hashed like everything else |
| `Tensor s δ` | a flat row-major buffer of magnitudes, its shape `s`, one shared dimension vector and hint | `s` is a type-level list of lengths. `Vec n δ` and `Mat m n δ` are how `Tensor [n] δ` and `Tensor [m, n] δ` print; rotations are `Mat 3 3 1` |

There is no unit type `()` because there are no effects. There are no strings
because nothing consumes them. There is no `Int` separate from `Num`: an integer is
an exact rational with denominator 1, and positions that need an integer (the
exponent of `^`, the argument of `noise` and `gauss`) are syntactic restrictions,
not types.

Declared types are the data types; `case` (§2.3) is how they are consumed.
`Bool`, tuples and lists are declared types the compiler holds (§2.3), and
differ from the others only in having syntax of their own; at runtime a
boolean is a constructor with no fields like any other.

### 3.2 Magnitudes: exact rationals and affine forms

A magnitude is one of two things.

**`Exact Rational`.** Produced by literals, units, `+ - * /`, integer `^`, `abs`,
`floor`, `ceil`, `round`, and by any operation whose inputs are all exact. Exact
values compare exactly, and stay exact while they are short: an exact result
of `+ - * /` or `^` longer than a size tied to the precision is rounded to
working precision instead, the rounding a bound nudge (§3.2.8, "exact while
small").

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
linear arithmetic by exactly the same rules. A non-linear operation keeps them
apart (decided by the owner).

- **The statistical model is the GUM's,** stated: each statistical nudge is an
  independent random variable of mean 0 and standard deviation 1, a shared
  nudge being one variable, and a value's statistical part is a linear model
  in them. Statistical nudges propagate to first order only, the GUM's law
  of propagation of uncertainty, `σ_f² = Σ (∂f/∂xᵢ)² σᵢ²`: the same model as
  the linear covariance propagation of `propagateCov2`.
- **A σ never becomes a bound.** The remainder of a non-linear operation that
  comes from bound nudges and slack alone is a rigorous bound, as before. A
  remainder computed as if a statistical nudge lay in `[-1, 1]` would turn a
  σ into a certainty (`n*n` for `n = 0 ±σ 1` was `0.5 ± 0.5`, and `(n*n) < 2`
  was `true`), so the part involving a statistical nudge is not folded into
  a bound.
- **Non-linearity is detected, not hidden.** Each non-linear operation
  estimates its second-order statistical term (for a product, `√((Σaᵢ²)(Σbᵢ²)
  + (Σaᵢbᵢ)²)` over the statistical coefficients; for a function, `|f''(m)|·
  σ²`) and compares it with the first-order σ. Under a threshold (1% by
  default) the result is a first-order σ and means what it says. Over it the
  value is marked **non-linear**: it prints with a warning, `:budget` says
  which operation made it so, and a comparison at a stated sigma refuses
  rather than decides (§3.2.9), since a mean and a σ no longer describe a
  skewed result. The mark propagates to everything computed from the value.
  The mark is re-judged, not inherited (decided by the owner, 2026-11-01):
  a value keeps the absolute size of the second-order statistical terms it
  carries, each with the operation that made it, and every later operation
  carries those sizes through as it carries its coefficients (scaled by the
  operation's slope) and compares them again with the value's own
  first-order σ. A term that later operations make negligible, against a σ
  that has since grown, stops marking; a product of two zero-mean `±σ`
  values still marks what it makes directly, but no longer every value
  computed downstream of it.

  *Re-judged, as built (2026-11-01, `Metron.Affine.SecondOrder`).* A
  value carries, for each operation that made a second-order statistical
  term, an upper bound on that term's standard deviation in the value's
  own unit, rounded up to three digits, or unbounded. A product's term is
  `√((Σaᵢ²)(Σbᵢ²) + (Σaᵢbᵢ)²)`; a function's is the largest change of
  `f'` from `m` to `m ± σ`, times σ, or its curvature bound across the
  σ-widened enclosure times σ², whichever is larger; a mixed correction's
  (below) is its size. Every operation carries its operands' terms:

  - a scaling by `k` multiplies them by `|k|`, and a sum adds them, term
    by term under each operation's name;
  - a product scales each operand's terms by the other factor's largest
    size, `|m| + r + σ + q`: its midpoint, bound radius, σ and the total
    of its own terms;
  - a function scales them by the largest `|f'|` over the operand's bound
    enclosure widened by `σ + q` on each side, unbounded when that
    reaches a pole or leaves the domain.

  Where the value is used (printing, `:budget`, a comparison, `floor`,
  `mid`, `sd`, the covariances), the sum of its terms is compared with its
  own first-order σ (`skewOf`), unbounded when that σ is zero, and the
  mark names the operation whose term is largest. A term below the
  precision floor where it is made is not recorded, as before; a carried
  term is never dropped, only re-judged. Dropping carried terms against
  the floor of a later midpoint would hide a real one: at `1e30` the floor
  is about `1e6`, and `(n*n + 1e30) - 1e30` would print an exact `0`.

  *Why it does not under-mark a real non-linearity in the cases tested.*
  Two rules. Sizes add: by Minkowski's inequality the standard deviation
  of a sum of random terms is at most the sum of theirs whatever their
  correlation, so a term that two operands share (`n*n + n*n`, perfectly
  correlated) counts at its full size, never in quadrature. And a term is
  scaled by the largest slope over the widened enclosure, not by the slope
  at the midpoint, which at a stationary point is zero and would drop a
  term that the next order keeps: `n*n*n` (the factor `n` has midpoint 0;
  its σ keeps the term) and `cos (n*n)` stay unbounded. A first-order σ
  that cancels leaves the term the whole value, unbounded: `x * (4 - x)`
  at `2 ±σ 1e-3`, `(n*n + m) - m`. Every mark in the suite stays. The
  price is overstatement where terms of opposite sign cancel, which sizes
  cannot show: a composition's steps add, where the old rule took the
  largest. `atan2` at 45° with σ a thirtieth of the radius reads 13% (7%
  before; its term is 2.4%); `asin` as `atan (x / √(1 − x²))` read 31%
  for a term of 5%, so `asin` is now lifted itself, its curvature
  `|t| / (1 − t²)^(3/2)`, and reads 5.8% (12% before).

  | value (`a`, `b`, `n` each `0 ±σ 1`) | before | after |
  |---|---|---|
  | `a * b`, `n * n` | unbounded | unbounded |
  | `a * b + (0 ±σ 1000)` | unbounded, `mid` and `<` refuse | `0 ±σ 1000`, not marked; `< 5000` is `true` |
  | `a * b + (0 ±σ 10)` | unbounded | 10% |
  | `n * n * n`, `cos (n * n)`, `n * n + n * n` | unbounded | unbounded |
  | `el.e` of `fromState` on `[7000, 100, 0 ±σ 1] km`, `[0.01, 7.5, 1 ±σ 0.0001] km/s` | refused: `circ` "marked non-linear by mul" | `0.016428 ±σ 1.8e-5`, not marked |
  | `tanh (5 ±σ 0.1)`, `exp (0 ±σ 0.1)`, `(1 ±σ 0.1) * (1 ±σ 0.1)` | 24%, 11%, 7.1% | the same |
  | `asin (0.99 ±σ 0.001)` | 12% | 5.8% |

  The Kepler solvers (`meanToEccentric`, `meanToHyperbolic`) took `mid`
  of their residual on the values. On a `±σ` input that residual's first
  order cancels, so it is now rightly marked, and `mid` refuses it. They
  bound `|f(E)|` by the residual at the midpoints and twice the bound
  radius of the residual on the values: rigorous, since the first lies in
  the second's enclosure.
- **Monte Carlo is the answer for the non-linear case** and is deferred:
  `:sample expr` would draw the statistical nudges from their distributions,
  evaluate the expression many times and report quantiles, the GUM's
  Supplement 1 method (§11).

*As built* (`Metron.Affine`):

- **The bound enclosure.** Every non-linear remainder and every domain check
  uses the bound enclosure `mid ± (Σ_bound |cᵢ| + slack)` only: the
  remainders of `mul`, `recip`, `sqrt`, `exp`, `log`, the circular and
  hyperbolic functions, `abs`, the Rodrigues series and `expm`'s norm bound,
  and the refusals of division, `sqrt`, `log`, `asin` and `atan2`, a chart's
  step and the pivots of `det` and `inverse`. So `1 / (1 ±σ 1)` is no
  division by zero: it is `1 ±σ 1`, marked non-linear by `recip`.
- **Three parts of a remainder.** Bound by bound is a fresh bound nudge, as
  before, with the midpoint's rounding. A part that is first order in a
  statistical nudge but scaled by a bound one, a product's `Bₓ·S_y`, or a
  function's slope changing across the bound enclosure, has size
  (`rB(x)·σ(y) + rB(y)·σ(x)` for a product, the slope's largest change over
  the bound enclosure times σ for a function, plus the slope's own
  approximation error times σ). This correction shares the original
  randomness, so it is not added as an independent statistical nudge.
  Instead its size is measured relative to the retained first-order σ;
  it is unbounded when that σ is zero. Above the configured threshold,
  `sd`, `mid`, comparisons and covariance summaries refuse the result.
  Below it, the reported σ is explicitly the first-order approximation,
  not a worst-case σ over the bounded coefficients.
  Statistical by statistical is second order and is not carried.
- **The measure.** A product measures `√((Σaᵢ²)(Σbᵢ²) + (Σaᵢbᵢ)²)` against
  the first-order σ; a function measures the largest change of `f'` from
  its midpoint to either `m − σ` or `m + σ`, against `|f'(m)|`, unbounded when
  either point leaves the domain (`recip`, `sqrt`, `log`) or when `f'(m) =
  0` (`cos` at 0). `abs` is linear unless its kink lies within σ of the bound
  enclosure, then unbounded. ~~The measure is kept squared and exact,
  rounded up to three digits, and a value keeps the largest measure, with
  its operation, of everything it was computed from (`Skew`).~~ Each term
  is carried as an absolute size and re-judged against the value's own σ
  where it is used (the mark is re-judged, as built, above). Functions with a
  second-derivative bound (`sin`, `cos`, `tan`, `atan`, `tanh`) also use
  that bound across σ, so equal endpoint derivatives cannot hide
  oscillation: the largest `|f''|` over the bound enclosure widened by σ on
  each side, against `|f'(m)|` (as built in §3.2.8: once the bound over the
  whole line, which overstated `atan (75 ±σ 0.075)` a hundred-thousandfold;
  `atan2` also divides by the larger operand, and `tan` and `tanh` are
  lifted themselves rather than as quotients). A zero first-order model
  does not establish equality if it has discarded a statistical remainder,
  even below the warning threshold. In particular `n*n == n*n` is currently
  undecidable: discarded remainders have no identity. Linear cancellation
  such as `n - n` remains exact.
- **The floor.** A second-order term whose absolute size is within the
  last of `p` significant digits at the value's midpoint (§3.2.8) is
  arithmetic noise and is not measured, whatever the first-order σ: one
  that cancelled exactly is noise of the same size, and the ratio of two
  noises is no measure. So `x * (4 - x)` for `x = 2 ±σ 1e-15`, stationary
  at 2 with a second-order term of `1.4e-30`, prints `4`; with `±σ 1e-3`
  the term is `1.4e-6`, real and visible, and it is marked. At a midpoint
  of zero there is no floor: `n*n` is all second order and stays marked.
  The floor does not unmark a term that is significant but cancels against
  another discarded term. `G * m` with a mass `m = iau2015.earth.mu / G`
  (in `astro`) is exactly the GM, but its product's second-order term,
  `−GM (δG/G)²`, about `7e-10` of the value, is cancelled only by the
  `+GM (δG/G)²` that `recip` discarded, which a first-order form does not
  carry. It stays marked; write the GM. Carrying second-order
  statistical coefficients, so that `ε²` cancels as `ε` does, would fix
  it, and is not done.
- **The threshold** is `:set nonlinear` in percent, default 1, and is
  applied where a value is used, not where it is computed: printing adds
  "(non-linear: mul, second-order term 7.1% of the first-order σ; a mean and
  a σ do not describe it)"; `:budget` adds the same line; a comparison, and
  `floor`, `ceil` and `round`, which are comparisons with the integers,
  refuse; and `mid`, `sd`, `covariance`, `crossCovariance` and `:covariance`
  refuse, so that `sd (n*n)` is not a
  misleading `0`. `bound` still answers: the bound part is rigorous. A
  value whose first-order σ is zero after such a step, `n*n`, prints its
  midpoint without the `…` that would promise every digit (§3.2.10):
  `5 (non-linear: mul, …)` for `n*n + 5`.
- **Rounding to integers** is decided as a comparison is, at the stated
  sigma: `floor (2.5 ±σ 0.17)` cannot be decided at sigma 3, where it was
  once decided by treating σ as a radius.

Otherwise the kinds differ only when a value is collapsed for printing,
comparison, budget or covariance. This is affine arithmetic in the
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

A quotient of proportional forms is exact for the same reason: `x / x` is
`1` and `(3 * x) / x` is `3`, because the same named nudges are the same
unknowns. Two conditions come first. The denominator's enclosure must
exclude zero: with `x = 1 ± 1`, `x / x` and `0 / x` are a division by zero,
as `1 / x` is, since some value in the enclosure is zero. And only named
nudges cancel: slack is anonymous, so two forms with equal slack are not
one unknown, and a denominator with slack takes the general path, a
product with the reciprocal (§3.2.2).

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
   the same fresh nudge, including the rounding that keeps the result's
   rationals short (§3.2.8).

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
`pi` and `e`, at `sqrt` of a non-square, at `±`, `±σ`, `noise`, `gauss`, and
at an exact result too long to keep (§3.2.8, "exact while small").
Approximation is
contagious through arithmetic. A program that never touches those, and whose
exact numbers stay short, stays exact.

#### 3.2.4 Nudge identity is content-addressed

There is no global counter. Evaluation is pure, so a nudge id must be a function
of what created it.

- **Builtin approximations**: `id = hash(builtin, operand midpoints, operand nudge
  ids and coefficients, working precision)`. Two evaluations of `sin 1` at the same
  precision produce the same nudge, so `sin 1 - sin 1 = 0`. This is correct: the
  approximation error of a deterministic algorithm on identical input is the same
  error. The hash is over a tagged, length-delimited encoding of the whole
  operation: the builtin's name, the precision, the number of operands, and
  each operand with a tag for its kind (exact, or affine with its midpoint,
  its nudges' ids and coefficients, and its slack) and every field
  length-prefixed, rationals as numerator and denominator. Two different
  operations never encode to the same bytes: operand lists `[1, 12]` and
  `[1/11, 2]` written end to end as text would, and their remainders would
  then cancel to an exact zero. Declared nudges' ids below use the same
  encoding. Nudge ids live only in values, never in the store.
- **Declared uncertainty** (`±`, `±σ`, `noise`, `gauss`): `id = hash(kind, hash of
  the enclosing top-level definition, path to the node inside it, component index,
  midpoint)`. Re-evaluating the same `±` with the same inputs gives the same
  nudge; `let f x = x ± 0.01` gives `f 2` one unknown and `f 3` another, since
  the midpoint is part of the identity, and a function's declared tolerance is
  not one number across all inputs.

  The codebase is content-addressed, so two definitions with identical text
  would be one definition and therefore one unknown. To keep `let a = 5 ± 0.1`
  and `let b = 5 ± 0.1` independent, as two parts from one batch are, the
  desugarer stamps every `±`, `noise` and `gauss` with the **full path of the
  definition it is written in** (`Owner "a"` at the root, `Owner
  "lab.offset"` in `namespace lab`, a field of the Core node, hence in the
  hash). The stamp is never printed: `:view a` shows `5 ± 0.1`, and
  re-adding that text under the name `a` reproduces the same term, while adding
  it under another name, or the same name in another namespace, makes a new
  measurement. The full path, not the last segment: `lab.offset = 1 ± 0.1`
  and `field.offset = 1 ± 0.1` are two instruments, and if they were one term
  and one unknown their difference would print as exactly `0`. The price is
  that renaming or moving a stamped definition changes its hash (§7.2). An expression typed at the
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
of the definition that created it (`G`, `astro.iers2010.earth`), or the builtin and reason
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
shares are quoted as fractions of `σ²`. With `:set precision 6`, `:use
astro`, `let mu = iers2010.earth.mu` (the IERS GM⊕, `±σ 8e5 m³/s²`) and
`let period a = 2 * pi * sqrt (a^3 / mu)`:

```
> :budget period (7000 km)
5828.5166380 ±σ 5.8e-6 (bound 3.4e-7) s
  kind   source               contribution  share
  σ      iers2010.earth @0.0  5.8e-6 s      100% of σ²
  bound  mul                  1.8e-7 s      52% of bound
  bound  recip                1.3e-7 s      39% of bound
  bound  pi                   1.9e-8 s      6% of bound
  bound  sqrt                 1.3e-8 s      4% of bound
```

#### 3.2.7 Compaction and slack

A long computation accumulates nudges. When a value carries more than `N` nudges
(default 64), the smallest coefficients are folded into `slack`, which is a plain
worst-case radius. This is always correct and slightly loose: the folded nudges
can no longer cancel. Statistical nudges are never folded: a σ must not quietly
become a bound. Rounding error from midpoint arithmetic and from shortening
coefficients (§3.2.8) does **not** go into slack: it joins the fresh nudge of
the operation that did the rounding, whose id
is content-addressed (§3.2.4), so two evaluations of the same operation round
the same way and `sin 1 - sin 1` is still exactly `0`. Slack never shrinks under
any operation.

#### 3.2.8 Working precision

Midpoints are rounded to `p` digits after every nonlinear operation, with the
rounding error accounted for (§3.2.7). This is the approach of the Arb library.
`p` is the `precision` setting plus guard digits (default `precision + 4`). A
value is therefore a pure function of the term and `p`. Exact values are not
rounded while they are short ("exact while small", below), and linear operations
on forms (`+`, `-`, scaling by an exact value) never round,
which is what keeps cancellation exact.

Every other rational a nonlinear operation produces is kept short too, at
`p + 4` significant digits:

- the function's value and slope at the midpoint, whose rounding joins their
  error bounds (a series summed in exact rationals is thousands of digits long);
- the size of the fresh nudge, rounded up, so a bound stays one;
- the bound coefficients of the result, rounded to a grid of `p + 4` digits of
  the value's size (the larger of its midpoint and its radius), and its slack,
  rounded up onto that grid. Their rounding joins the operation's fresh nudge.
  A coefficient below the grid becomes zero and its nudge leaves the value;
- the statistical coefficients, each to `p + 4` digits of its own size, so none
  vanishes. Their rounding is an error in a coefficient, like a slope's, and is
  measured against the first-order σ (§3.2), never made a bound.

Without this, lengths compound. A product's coefficients have the digits of
both factors, a sum of rationals with different denominators has the digits of
both, and the next operation evaluates its series at the enclosure's ends. An
iteration that uses a value several times, Newton's method for Kepler's
equation, then multiplied the length of every coefficient by about four per
step and its time by about ten (four steps took 110 s). With every rational
short, each step costs the same, and a value no longer keeps every nudge an
iteration ever made: the converged steps' leftovers fall below the grid.

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

**Exact while small** (decided by the owner, 2026-11-01). Every number is
made of rationals; working precision bounds how long they get, not what they
are. An exact result of `+`, `-`, `*`, `/` or an integer power stays exact
while its numerator and denominator stay short, within a size tied to the
precision (a few times `p` digits): `1/3 + 1/6` is exactly `0.5`, and exact
inputs give exact answers in ordinary use. When an exact result would grow
past that size, it is rounded to `p + 4` significant digits instead, the
rounding becoming a fresh bound nudge as any other operation's does, so an
exact iteration that doubles its digits each step (`x ↦ 3.7·x·(1 − x)`)
keeps running at working precision rather than growing without limit. A
value's magnitude is a separate matter: a number too large or too small to
write at all (`2^(2^64)`) is refused by the `digits` limit of §8.1, which
bounds the exponent, not the significant digits. Every built-in operation
and function is held to this: a non-linear function's result is always at
working precision (its value is rarely an exact rational), and no built-in
returns a rational longer than the precision allows unless it is exact and
short.

**Linear results are held to the same length** (decided by the owner,
2026-11-01). A linear operation on an affine form never rounds, which is
what keeps `x - x` exactly 0, but its midpoint and coefficients can still
grow: `x + 1/k` summed over k gives a midpoint whose denominator grows like
lcm(1..k). So the length limit above applies to a linear result's midpoint
and coefficients too: past it they are rounded to `p + 4` significant
digits, the rounding a fresh bound nudge, named and content-addressed as
any other operation's. Cancellation is unaffected in every case that
matters: `x - x` is exactly 0 always, since equal forms cancel term by term
before any length is measured, and `(x + c) - x` is exactly `c` whenever
the midpoints were short.

*Linear results held, as built (2026-11-01, `Metron.Affine.heldLinear`).*
`addM`, and so `subM` and `sumM`, and `scaleM` on a form compute the
linear result exactly, equal terms cancelling first, then measure the
length (`exactLength`) of its midpoint, every coefficient and the slack.
Past `exactLimit`, 224 digits at the default precision, all of them are
rounded as a non-linear result's are (`shortenLinear`): the midpoint to
`p + 4` significant digits, the bound coefficients to a grid of `p + 4`
digits of the value's size and the slack up onto it, the statistical
coefficients to `p + 4` digits of their own, away from zero: the σ is
never understated nor made a bound, and no correction is left to carry
(§3.2), which at a midpoint of zero, where there is no floor, would have
kept a held `0 ±σ 1` scaled a hundred times from cancelling with itself.
The bound
rounding is a fresh nudge named `add: rounding` or `mul: rounding`,
addressed by the operation, its operands (a sum's in the order of their
encodings, so `a + b` and `b + a` are one unknown) and the precision.

One rule the decision did not name: a value's earlier roundings of linear
results join the new one. Without it a loop that rounds every few dozen
steps added a nudge each time until the 64 were full, and compaction
folded them into slack, which is anonymous and does not cancel: the
harmonic sum minus itself printed `0.0000000000000000000…`, not `0`.
Joining is sound, a coefficient becoming part of a bound, and forgets
only those roundings' correlation with other values. So `x - x` is `0`
for every form without slack, however long, and `(x + c) - x` is `c` when
the midpoints are short and an enclosure of `c` when they are not
(`c = 1/7^300 + 1/3`).

Wall time of the executable under a 4 GB cap, before → after; peak RSS is
31 MB in every case, before and after, so memory is constant:

| program | before | after |
|---|---|---|
| `H₃₀₀₀₀`, `x + 1/k` summed on `x = 0 ± 0.001` | 6.6 s (13 s in the audit) | 0.20 s |
| `H₆₀₀₀₀`, `H₁₂₀₀₀₀` | 39 s, — | 0.30 s, 0.52 s |
| `Σ xᵏ/k`, `x = 999/1000`, exact terms `t * x`, to 3000, 30000, 60000 terms | 2.9 s, past 300 s, — | 0.16 s, 0.80 s, 1.7 s |
| `t * 0.999` ten thousand times, `t` a form compared each step | 30 s | 0.18 s |
| `Σ xᵏ/k!`, `x = 1/3`, exact terms, on `1 ± 1e-30`, 3000 and 6000 terms | 1.1 s, 6.3 s | 0.59 s, 2.0 s |

The last is not linear in the number of terms, and not because of a
length: its term `1/(3ᵏ k!)` is exact and short, its numerator being 1,
but its size grows by about `log k` digits a step, and every step pays
for the size. The `digits` limit (§8.1) bounds that.

**§3.2.8 exact while small, as built (2026-11-01).**

*The rule* (`Metron.Affine.exactResult`). An exact result's length is the
shorter of its numerator and denominator. Its size is the `digits` limit's
concern (§8.1), so `2^100000`, `1e-99999` and `1/3^300` are short, and the
cost of exact arithmetic is bounded by the size and twice the length
together. The limit is **eight times `p + 4` digits**, 224 at the default
precision (`exactLimit`). It was chosen by measurement: the longest exact
result of ordinary arithmetic in the test suite is 122 digits at the default
precision, the products of a spinning chart's exact rotation, which a test
then cancels in a finite difference, so the limit is about twice that; the
tutorial's output is unchanged. A product of eight values at working
precision stays exact, an exact operation at the limit costs about
sixty-four times one at working precision (microseconds), and an iteration
that doubles its length reaches the limit within `log₂ (8 (p + 4))` steps.
Past the limit the result is rounded to `p + 4` significant digits, and the
rounding is a fresh bound nudge named `add`, `mul` or `div` with the
operands (in order for a sum or a product, so `a + b` and `b + a` are one
unknown) and the precision. An integer power squares through `mul`, so
`(2/3)^1000` is exact until a square passes the limit and at working
precision after. `addM`, `subM`, `scaleM` and `sumM` take the precision.
Linear operations on forms ~~never round~~ round only past the same limit,
after equal terms cancel (linear results held, as built, above): `x - x`
is `0` and `(x + 1/3) - x` is `1/3`. A comparison takes the exact difference of its operands, never
rounded. What changes: a long exact value is now an enclosure, so
`(1/3)^500 + 1 - 1` prints `0.0000000000000000000…` (within one unit of the
true `2.7e-239`) where it printed the exact value.

*The logistic map*, `iter (1/3) N` for `x ↦ 3.7 x (1 − x)`: exact through its
seventh step, then at working precision, every step the same cost,
about 0.4 ms at precision 20 and 5 ms at 200. Twenty steps took 13.4 s and
now take 0.10 s; 250 steps at precision 200 agree with bc to every printed
digit. The map is chaotic: the enclosure grows at its Lyapunov rate, about
e^0.35 a step, until the 64-nudge cap folds nudges into slack, which then
grows by up to 3.7 a step. It is meaningful for about 100 steps at precision
20 and 250 at precision 200; beyond, it covers more than `[0, 1]`, the
square diverges, and the `digits` limit stops it. That is the rigorous
answer, not a cost.

*Series at working precision* (`Metron.Numerical.Approx`). Every series is
summed in fixed point, an integer counting units of `2^-b`, each step's
rounding counted in the bound (`fixedSum`, `oddPowerSeries`); in exact
rationals each term was longer than the last. π and `ln 2` are computed once
per precision bucket (64, 128, 256, … digits) and kept, rounded to the
precision asked. `sin` and `cos` reduce modulo `π/2` with π to as many more
digits as the angle has before its point, and again as many as the reduced
angle has zeros after it. `log` puts its reduced argument in fixed point at
once. `sqrt` takes the root of a number of about `2p` digits, whatever the
argument's length. `tan` and `tanh` are new approximations, with their
slopes. `decimalExponent` estimates from bit lengths and corrects, where it
counted by tens. `Metron.Encode.sint` encoded a long integer a byte at a
time, copying it once per byte: a nudge id over `1e-99999` took 1.25 GB; it
splits in halves now, byte for byte the same encoding. The old
exact-rational series are kept as a test oracle (`test/Support/ExactApprox.hs`):
for random arguments the two enclosures overlap.

*Results that kept long rationals.* A product whose every linear coefficient
fell below the grid (§3.2.7) left its base without nudges, and `withFresh`
then skipped rounding the midpoint: a step of the logistic map kept a
115-digit midpoint. Such a midpoint is shortened to `p + 4` digits now.
`enclose` shortens its value as any operation's result is, so `expm`'s
series, scaled by `1/k` and summed, no longer keeps the digits of
`lcm (1, …, K)`. `inverse`, whose last step is linear, settles its
non-exact entries the same way, each with a nudge named by its position.

*The second-order estimate for `atan2`* (§3.2) was wrong. For `y = 1 ±σ
0.001`, `x = 0.03 ±σ 0.001` the angle's Hessian is about `[[0.06, 1], [1,
−0.06]]` and its gradient about `(−1, 0.03)`, so the second-order term's
standard deviation, `σ² √(½ tr H²)`, is `1e-6` against a first-order σ of
`1e-3`: 0.1%. It reported "second-order term 120000%", for two reasons.
`atan2` took `atan (y/x)` whenever `x > 0`, a quotient near 33 whose own
curvature (7%, real) the arctangent then undoes; and `atan`'s measure used
its bound over the whole line, `|atan''| ≤ 0.65`, against its slope
`1/(1 + 33²)`. `atan2` now takes the arctangent of the smaller operand over
the larger by midpoint, falling back to the other when the divisor's
enclosure may be zero. Every function lifted with a curvature bound (`sin`,
`cos`, `atan`, and now `tan` and `tanh`) bounds `|f''|` over the bound
enclosure widened by σ on each side. `tan` and `tanh` are lifted themselves:
as quotients, `tanh (5 ±σ 0.1)` was marked 78000% where its term is 20%
(the numerator's and denominator's σ cancel in the quotient to first order
but not in the product's measure). The product's measure,
`√((Σaᵢ²)(Σbᵢ²) + (Σaᵢbᵢ)²)`, is exact for a product of two linear forms
(Isserlis), so `*` was right; `/`, `*` of a reciprocal, overstates by about
√2; a composition takes the largest of its steps' measures, so `asin (0.99
±σ 0.001)` reads 12% against 5%, and `atan2` at 45° with σ a thirtieth of
the radius 7% against 2.4% (since the mark is re-judged, §3.2, a
composition adds its steps' terms: `atan2` there reads 13%, and `asin`,
lifted itself, 5.8%). Measured after, against `|f''| σ / |f'|`:

| value | before | after | `\|f''\| σ / \|f'\|` |
|---|---|---|---|
| `atan2 (1 ±σ 0.001) (0.03 ±σ 0.001)` (lengths in m) | 120000% | not marked | 0.1% |
| the inclination of a near-polar orbit from `fromState` on a `±σ` state | 43000% | not marked | about 0.002% |
| `atan (75 ±σ 0.075)` | 42000% | not marked | 0.2% |
| `tanh (5 ±σ 0.1)` | 78000% | 24% | 20% |
| `asin (0.99 ±σ 0.001)` | 1800% | 12% | 5% |
| `sin ((0.01 ±σ 0.02) rad)`, `cos ((1.5 ±σ 0.02) rad)` | 2%, 2% | not marked | 0.02%, 0.14% |
| `tan ((1.5 ±σ 0.001) rad)` | 2.9% | 2.9% | 2.8% |
| `exp`, `log`, `sqrt`, `sinh`, `cosh` at `5 ±σ 0.1` | 11%, 2%, 1%, 11%, 11% | the same | 10%, 2%, 1%, 10%, 10% |

`tan` of an enclosure that reaches a pole is a domain error ("reaches a pole,
an odd multiple of π/2"), where it was a division by zero; a σ that reaches
one makes the value unbounded.

*The audit.* Each built-in: whether its result is at working precision (no
rational longer than `p + 5` digits unless exact and short), whether every
rounding is in its bound, how its internals run, and its cost: the wall
time of the executable at precisions 20, 50 and 200, including about 0.09 s
to start, before → after where it changed. "0.1 s" is the start alone.
Tested at those precisions against bc to 260 digits (every printed digit
within one unit of the last, as many digits as the precision), and at
working precisions 24, 54 and 204 for the length of every rational, from an
exact argument, one with a bound and one with a σ (`test/Precision.hs`).

| built-in | result | roundings | internals | cost at 20, 50, 200 | fix |
|---|---|---|---|---|---|
| `+`, `-`, `neg` | exact while short; forms linear, held to the limit | an exact result's rounding is a nudge, `add`; a form's, `add: rounding` | — | 0.1 s | exact while small; linear results held |
| `*`, `emul`, `scale`, `outer` | exact while short; a form scaled held to the limit; a product of forms shortened | `mul`; `mul: rounding`; the product's remainder | — | 0.1 s | exact while small; linear results held |
| `/`, `ediv`, `to` | exact while short; otherwise `*` and `recip` | `div`; `recip` | — | 0.1 s | exact while small |
| `^` (integer) | squaring through `*` | each square's | `log₂ n` products | 0.1 s (`(2/3)^1000`) | exact while small |
| `sqrt` | working precision; exact for squares | yes | integer root of `2p` digits | 0.1 s; `sqrt 1e-99999` 24 s, 924 MB → 0.14 s, 19 MB | root at relative precision |
| `exp` | working precision | yes | fixed point; squares rounded at their own digit | 0.1 s | fixed point |
| `log` | working precision | yes | fixed point; `ln 2` kept | 0.1 s; `log 1e-99999` 28 s, 104 s, past 120 s → 0.1 s | argument in fixed point; encoder |
| `sin`, `cos` | working precision | yes | reduction mod `π/2`, π kept; fixed point | 0.1 s; `sin 1e10` at 200, 1.5 s → 0.1 s | fixed point, π kept, local curvature |
| `tan` | working precision | yes | sine over cosine, at more digits near a pole | 0.1 s | lifted itself |
| `asin`, `acos` | working precision; `acos` is `π/2 − asin` | yes | lifted itself, its value `atan (x / √(1 − x²))` at the midpoint, its curvature `\|t\| / (1 − t²)^(3/2)` | at 200, 4.7 s → 0.1 s | lifted itself (the mark re-judged) |
| `atan` | working precision | yes | fixed-point halvings and series | at 200, 1.0 s → 0.1 s | local curvature |
| `atan2` | working precision | yes | as `/` and `atan` | at 200, 1.5 s → 0.1 s | the larger operand divides |
| `sinh`, `cosh` | working precision | yes | series near zero, `exp` beyond | 0.1 s | fixed point |
| `tanh` | working precision | yes | sine over cosine near zero, `(1 − q)/(1 + q)` beyond | 0.1 s | lifted itself |
| `pi` | working precision | yes | Machin in fixed point, kept per bucket | 0.1 s | kept |
| `abs` | linear, or one nudge across zero | yes | — | 0.1 s | — |
| `floor`, `ceil`, `round` | exact integers | decided as comparisons | — | 0.1 s | — |
| `==`, `/=`, `<`, `<=`, `>`, `>=` | booleans | the exact difference, never rounded | — | 0.1 s | exact difference |
| `norm` | `sqrt` of a sum of products | yes | — | 0.1 s | — |
| `dot` (`·`, `@`), `contract`, `transformBy` | sums of products | yes | — | 0.1 s | — |
| `wedge`, `cross` (`star (a ∧ b)`), `star` | differences of products | yes | — | 0.1 s | — |
| `inverse` | working precision | yes, and a settling nudge per entry | Gauss–Jordan | 0.1 s | entries settled |
| `det` | working precision | yes | elimination, product of pivots | 0.1 s | — |
| `cholesky` | working precision | yes | Cholesky–Banachiewicz | 0.1 s | — |
| `expm` | working precision | yes | Rodrigues for one plane; else the series in affine arithmetic, each term a matrix product of forms with up to 64 nudges | exact 2 × 2 0.1 s; 2 × 2 of `sqrt`s 0.13, 0.23, 3.5 s; 3 × 3 0.23, 0.65, 13 s (unchanged) | `enclose` shortens |
| `covariance`, `crossCovariance` | exact by definition: products of coefficients of `p + 4` digits | none | — | 0.1 s | — |
| `mid`, `bound`, `sd` | exact; `sd` a root at working precision unless the variance is a square | `sd`'s root | — | 0.1 s | — |
| `noise`, `gauss`, `±`, `±σ` | unit or declared coefficients | — | — | 0.1 s | — |
| `seq`, `vmap`, `vzipWith`, `timap`, `indices`, `transpose`, `permute`, `slice`, the chart primitives | structural, or sums and products above | inherited | — | 0.1 s | — |

There is no `min` or `max` function (`min` is the minute); the library's
functions (`cross`, `trace`, `asinh`, …) are compositions of these.

*Left open.*

- **A linear loop on a form grows.** The owner's rule keeps linear operations
  on forms unrounded, so `x + 1/k` for an affine `x` collects the
  denominators: `H₃₀₀₀₀` summed exactly, which rounds once past the limit
  and is a form after, takes 13 s before and after, its midpoint's
  denominator about `lcm (1, …, k)`. A series written in the language from
  exact terms, `Σ xᵏ/k!`, takes the same path. A proposal for the owner:
  hold a linear result's midpoint and coefficients to the same limit,
  rounding past it with a fresh nudge named by the operation and its
  operands. `x - x` stays `0`, and `(x + c) - x` stays `c` whenever the
  midpoints are short. *Done* (decided by the owner and built, 2026-11-01:
  linear results held, as built, above): `H₃₀₀₀₀` takes 0.20 s.
- **`expm` with uncertain entries is slow at high precision**: 13 s for a
  3 × 3 at precision 200, as before. A product of forms with 64 nudges costs
  milliseconds there, and the series takes about a hundred terms, a matrix
  product each. Evaluating the polynomial with about `2√K` matrix products
  instead of `K` (Paterson–Stockmeyer) is the likely fix; not measured.
- **A product of two zero-mean statistical values is marked unbounded**, and
  the mark survives a sum in which that product is negligible (a value keeps
  the largest measure of everything it was computed from, §3.2): `fromState`
  on a state with `0 ±σ 1` components marks the eccentricity and refuses its
  comparisons. The product's estimate is right; carrying the second-order
  term's absolute size, scaled by each later slope, and comparing it with
  the final σ would be the change. A question for the owner. *Done*
  (decided by the owner and built, 2026-11-01: the mark re-judged, as
  built, §3.2): that eccentricity is `0.016428 ±σ 1.8e-5`, unmarked.
- **A composition overstates its second-order term** (since the mark is
  re-judged, §3.2): its steps' sizes add, while their terms may cancel in
  part. `atan2` at 45° with σ a thirtieth of the radius reads 13% for a
  term of 2.4%. Lifting a function itself, as `tan`, `tanh` and `asin`
  are, is the fix where it matters; carrying signed second-order
  coefficients, a quadratic form in the nudges, would be the general one.

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
A difference marked non-linear (§3.2) is never decided, since a mean and a σ
do not describe it: "cannot decide comparison at sigma 3: the difference is
marked non-linear by mul". `floor`, `ceil` and `round` are comparisons with
the integers and are decided the same way.
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
**builtins** of dimension L, M and so on, written `Num m`, `Num kg`, … (§4.1).

The SI declares the radian dimensionless, so that `s = r θ` and `sin θ` read as
the formulas are written. We give angle a dimension instead, as Boost.Units does,
because the calculator's job is to catch the mistakes the formulas invite: `sin 1`
is an error that asks for `1 rad` or `45 deg`, angular velocity `rad/s` and
frequency `Hz` are different types that cannot be added or confused by a factor
of 2π, and `sr = rad^2` makes the photometric units honest. The price is that an
angle must be divided out where the SI quietly drops it: arc length is
`r * θ / 1 rad` and angular velocity from a speed is `v / r * 1 rad`, the
same bookkeeping every other dimension already asks for. The base units are
units, of type `Unit m` and so on (§3.10, part U). Everything else is prelude
source written in the language itself and therefore hashed, viewable and
rebindable:

```
unit N  = kg*m/s^2              -- a unit from a unit
unit J  = N*m
unit W  = J/s
unit Pa = N/m^2
unit km = 1000 m                -- a unit from an amount, its size
unit g  = 1 kg / 1000           -- the one wrinkle: the base unit carries a prefix
```

The prelude, now the standard library split by domain into namespaces (§7.7), ships: in `si`, the 22 derived SI units (N, J, W, Pa, Hz, C, V, Ω, F, S, T, H,
Wb, lm, lx, Bq, Gy, Sv, kat, with `sr = rad^2` in `angle`), each also under
its name (`newton`, `joule`, …), the 24 SI prefixes as numbers (`kilo`,
`milli`, …) applied to every base and derived unit plus `L` and `g` (`unit
km = kilo * 1 metre`, `mm`, `µs`, `kPa`, `GHz`, …); and the accepted units
iapetus needs: `min hr day year` (Julian, 365.25 day; `h` is the hour's
symbol) in `time`, `AU` in `astro`, `deg arcmin arcsec` in `angle`, `L`, `t`
in `si`. The prefix table is generated by `Metron.Prelude`, not typed by hand.

Measured constants are library definitions (`astro.G`, reached with `:use astro`) **with `±σ`** taken from CODATA
standard uncertainties, so uncertainty is present by default, carries the
statistical kind, and `:budget` can name it: `G = (6.67430e-11 ±σ 1.5e-15) *
1 m^3 kg^-1 s^-2` (CODATA 2018, unchanged in 2022). The bodies' constants
are in the constant sets of `astro` (§7.7), measured ones with their published
`±σ`; a mass is derived where it is wanted, `iau2015.earth.mu / G` from the
exact IAU nominal GM, so its uncertainty is G's and the budget says so
(`5.97217e24 ±σ 1.3e20 kg`). Angles:
`unit deg = pi / 180 * 1 rad`, `arcmin`, `arcsec`, so `90 deg` prints as itself
and `sin (90 deg)` is `1.00000000000000000000…`. CODATA publishes 1σ values, which are not hard bounds;
shipping them under `±` would let a 68% band print as a certainty, so the prelude
never does that. Exact-by-definition constants (`c`, `h`, `k_B`, `N_A`, `e_charge` in `physics`
since SI 2019; the IAU *nominal* values in `astro.iau2015`, and the defining
parameters of `astro.wgs84`) ship as exact rationals
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
  `unit km = 1000 m`. Its term is a unit, `Unit m` (§3.10, U7): the
  declaration makes its body, an amount or a unit, a unit, so `unit dozen =
  12` and `let eggs = 12` are two terms, a `Unit` and a `Num`. That it is
  its own display unit is a property of the **name**, label-level metadata
  in the codebase like the binding itself, not part of the hash: `Bq` and
  `Hz` are one term, `s^-1`, yet each prints as written. What makes this
  possible is that every reference in Core carries the name the author
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
  is `180`, `(2 km)^2 / 1 m` is `4000 km`. (After a literal the quantity takes
  in the units that follow it, §2.6, so `90 deg / rad` is `90 (deg/rad)`,
  whose units cancel when the quantity is taken.) Unit arithmetic itself
  cancels nothing: the unit `km/m` prints as `km/m` (§3.10, U8).
- `+` and `-` take the **smaller** of their operands' units, so that the result
  does not depend on operand order: `5 km + 3 m` and `3 m + 5 km` are both
  `5003 m`. Projection, packing, negation, `abs`, `norm`, `transpose`
  and `⋆` keep the unit; every other operation drops it.
- `x to u` replaces the display unit with `u`'s; `u` is a unit (§3.10, U6),
  `x to km/h`, never an amount. `to` is shape-polymorphic. `:prefer` takes a
  unit too.

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

**The empty literal.** `[]` is a tensor of length zero whose element type
comes from context, as any literal's does: an ascription, `([] :: Vec 0 m)`
or `([] :: Mat 0 3 m)`, unification with another operand, `dot ([] :: Vec 0
m) ([] :: Vec 0 m)` is `0 m^2`, or a signature. Typed Core keeps a pack's
element type even with no elements (`TPack`), and an empty pack is built
from it (§8). A definition may leave it open, `let e = []` is `forall s d.
Tensor (0 : s) d`, each use choosing; an expression at the prompt whose
value leaves open, outside any function, a length, shape or dimension that
building it needs has no value to build, and is refused as a type error
(`Empty` of `data Box d = Empty | Full (Num d)` needs none, and is
built): "ambiguous: nothing fixes the
shape or dimension of this value, of type Tensor (0 : s) d; give an empty
tensor a type, as in ([] :: Vec 0 m)".

**Size.** A tensor has at most ten million components (`componentLimit`).
Lengths, counts and index positions are machine integers, so one written
past the limit (`noise 18446744073709551616`, `Vec 18446744073709551616` in
a signature, a projection `.18446744073709551616`, a position of `contract`
or `slice`) is refused where it is written, never wrapped, and a product
whose operands are each within the limit but whose result is not (`outer`,
`dot`, `wedge`) is refused when it runs: "the result would have 16000000
components: a tensor has at most 10000000 components".

Tensors are **homogeneous**: all components share one dimension. A position is
`Vec 3 m`, a velocity `Vec 3 (m/s)`, a rotation `Mat 3 3 1`. A six-element state
is the tuple `(r, v)`, not a `Vec 6`, and its covariance and state-transition
matrix, whose entries mix dimensions, are written as homogeneous blocks
(§3.7, which also records the type-system route, Hart's dimensioned
matrices, should blocks ever not be enough).

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
dot        : Vec n d1 -> Vec n d2 -> Num (d1*d2)
cross      : Vec 3 d1 -> Vec 3 d2 -> Vec 3 (d1*d2)
norm       : Vec n d -> Num d
transpose  : Mat m n d -> Mat n m d
inverse    : Mat n n d -> Mat n n (1/d)
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
covariance : Vec n d -> Mat n n (d^2)
crossCovariance : Vec n d1 -> Vec m d2 -> Mat n m (d1*d2)   -- the nudges two vectors share (3.5)
cholesky   : Mat n n (d^2) -> Mat n n d
contract i j : Tensor (l0 : … : lj : s) d -> Tensor (… without i and j : s) d
                                             -- i < j literals, li = lj; a trace (§4.2)
permute [p0, …, pk-1] : Tensor (l0 : … : lk-1 : s) d -> Tensor (lp0 : … : lpk-1 : s) d
                                             -- the p a literal permutation of 0 .. k-1
slice k i  : Tensor (l0 : … : lk-1 : n + i + 1 : s) d -> Tensor (l0 : … : lk-1 : s) d
                                             -- k, i literals; written t._.i with k wildcards (§2.10)
trace      : Tensor (n : n : s) d -> Tensor s d   -- prelude: trace a = contract 0 1 a
expm       : Mat n n -> Mat n n              -- the matrix exponential, dimensionless; a rotation from a bivector
transformBy : Mat n n -> Tensor s d -> Tensor s d   -- R along every axis: R v, R P Rᵀ, …; every length must be n; anonymous axes only (3.9)
e1 e2 e3   : Vec 3                           -- linalg: the unit vectors
rotx roty rotz : Num rad -> Mat 3 3        -- linalg: the bivector of a turn about an axis, right-handed; over any one three-axis set (3.9)
dual       : Tensor (3 : s) d -> Tensor (3 : 3 : s) d   -- linalg: dual v = ε @ v, the inverse of ⋆
axisAngle  : Vec 3 d -> Num rad -> Mat 3 3 -- linalg: the bivector of a turn about any axis
rotation   : Vec 3 d -> Vec 3 d1 -> Mat 3 3  -- linalg: the bivector taking a's direction to b's
euler313   : Num rad -> Num rad -> Num rad -> Mat 3 3   -- linalg: the 3-1-3 matrix
rotationOf : Chart c -> Mat s c              -- a chart's absolute rotation, rows along its space's base, columns along its frame's axes; I when not turned (3.8, 3.10)
v to c     : Vec s d1 -> Chart c -> Vec c d1    -- along the space's base axes to the chart's, Rᵀ v (once linalg.along; 3.10 F10)
v from c to c1 : Vec c d1 -> Chart c -> Chart c1 -> Vec c1 d1   -- along one chart's axes to another's, R1ᵀ R v (once linalg.inChart; 3.10 F10)
withAxes   : Chart c -> Vec n d1 -> Vec c d1   -- an anonymous vector read as along the chart's axes; no arithmetic (3.9)
rotateVec  : Mat b a -> Vec a d -> Vec b d   -- linalg: r v, typed by r's rows and columns (3.9)
rotateCov  : Mat b a -> Mat a a d -> Mat b b d   -- linalg: r p rᵀ, a covariance turned (3.9)
```

**Rotations.** A rotation is generated by a *bivector*: an antisymmetric
`Mat n n`, the oriented plane of the turn with the angle as its size, and
`expm` makes the rotation matrix from it. The constructors in `linalg`
build bivectors; `expm` and `@` turn them into matrices and compose them:

```
> expm (rotz (90 deg)) @ [1, 0, 0]
[3.0e-24 ± 3.8e-24, 1.0000000000000000000…, 0]
> rotz (30 deg) == axisAngle [0, 0, 1] (30 deg)
true
> rotation e1 e2 == rotz (90 deg)
true
> transformBy [[0, -1, 0], [1, 0, 0], [0, 0, 1]] [[4, 1, 0], [1, 9, 0], [0, 0, 1]]
[9, -1, 0; -1, 4, 0; 0, 0, 1]
> :type rotation
forall d d1 (a : 3) (b : 3). Vec 3 d -> Vec 3 d1 -> Mat a b
```

(The bivector's axes are free, `(a : 3)` and `(b : 3)`, because `dual`'s
`ε` is a literal and a literal takes its axes from use (§3.9, decision
5); its arguments are anonymous because `rotation` names a local value
built from `e1` and `e3`, which a named value's default makes anonymous.
Stage 4 of §3.9 generalises the rotation constructors over one axis set.)

- `a ∧ b` is stored as the matrix `a bᵀ − b aᵀ`, whose product with a
  vector turns `b` toward `a`: `(e1 ∧ e2) @ e1 = −e2`. So the generator
  of the turn from `a` toward `b` is `b ∧ a`, and `rotz θ = θ (e2 ∧ e1)`,
  `rotx θ = θ (e3 ∧ e2)`, `roty θ = θ (e1 ∧ e3)`, each of the angle divided
  by `1 rad` (the constructors write `(θ to rad) / 1 rad`, which fixes the
  argument to an angle). `expm (rotz (90 deg))` turns `e1` to `e2`: the
  right-hand rule. `⋆` keeps its sign (`⋆ (e1 ∧ e2) = e3`, so `cross` is
  unchanged), and so `⋆ (rotz θ) = −θ e3`.
- `dual v = ε @ v` is the inverse of `⋆` on bivectors (`⋆ (dual v) = v`,
  `dual v @ u = u × v`), and `b ∧ a = dual (b × a)`. `axisAngle n θ`, the
  turn by `θ` about `n` by the right-hand rule, is the dual of `−θ n /
  norm n`; `axisAngle [0, 0, 1] θ == rotz θ`. (`dual` is not the generator
  about `v`: that is `dual (−v)`, the matrix of `u ↦ v × u`.)
- `rotation a b` is the bivector of the smallest turn taking `a`'s
  direction to `b`'s: the plane `b ∧ a` divided by `norm (a × b)`, times
  the angle `atan2 (norm (a × b)) (a · b)`, written as the dual of `−φ (a ×
  b) / norm (a × b)`; only directions matter, so `a` and `b` may have
  different dimensions. When `a × b` is exactly zero, a parallel pair
  gives the zero bivector, and an antiparallel pair, for which every plane
  through `a` would do, half a turn in the plane through `a` and `e3`, or
  `e1` when `a` is along `e3`. Vectors that are nearly parallel within
  their enclosures make `==` undecided, which is reported; a zero vector
  divides by zero.
- Every constructor's bivector is *exactly* antisymmetric, as affine forms:
  `rotx`, `roty` and `rotz` scale an exact matrix, and `axisAngle` and
  `rotation` form one vector, angle included, and take its dual, whose
  entries are that vector's components and their negations. So `B + Bᵀ ==
  0` is decided true even for an uncertain angle or axis, which is what a
  chart's generator is checked against (§3.8). Written as `θ * dual …`, the
  scalar product would give each entry and its partner fresh nudges of
  their own, and the sum would be `0 ± 10⁻²⁷`, undecided. One caveat: an
  angle whose `±` radius is itself inexact (`30 deg ± 1 deg`, with `π` in
  the radius) carries that radius as slack (§3.2.7), which never cancels,
  so `B + Bᵀ` is then a tiny enclosure of zero rather than zero; `± 0.01
  rad` does not.
- `euler313 Ω i ω = expm (rotz Ω) @ expm (rotx i) @ expm (rotz ω)` is the
  matrix of the classical 3-1-3 sequence (the orbital elements' node,
  inclination and argument): it takes perifocal components to inertial
  ones. It returns the matrix, not a bivector, since two turns in different
  planes do not add as bivectors; each Euler sequence is its own function
  with the sequence in its name.

`expm` is exact where it can be and rigorous everywhere. It splits `B`
into its antisymmetric part `A` and symmetric part `S`. When `A` is a
single plane (always for `n ≤ 3`; checked exactly for an exact `A` beyond)
it uses Rodrigues' formula `I + f(t) A + g(t) A²` with `t = Σ_{i<j}
a_ij²`, the square of the angle, and `f = sin θ / θ`, `g = (1 − cos θ) /
θ²` written as their series in `t`, which have no singularity: an angle
whose enclosure holds zero (`rotz (0 rad ± 0.001 rad)`) divides by nothing.
`S` is exactly zero for every constructor's bivector; when it is not but
is below the printed precision (a bivector built entry by entry through
products, whose two halves got fresh nudges of their own, or one carrying
slack), each entry gets a fresh nudge of `2σ`, `σ` the bound of `S`,
since `‖exp (A + S) − exp A‖₂ ≤ e^σ − 1` (`exp (τA)` is orthogonal, and
the logarithmic norm of `A + S` is at most `σ`). Any other matrix takes the
exponential series with scaling and squaring: `β` is the ∞-norm (largest
row sum) of `|midpoint| + radius`, which bounds the norm of every matrix
in the enclosure; `B / 2ˢ` has `β / 2ˢ ≤ 1/2`; the series is summed to
the first term `K` with `β'ᴷ / K!` below the working precision plus a
digit per squaring; the remainder, at most `2 β'ᴷ / K!` in ∞-norm and so
in every entry, is a fresh nudge of each entry's own; and the result is
squared `s` times. Each product's coefficients are shortened as every
nonlinear operation's are (§3.2.8), so the series carries rationals of
bounded length. An angle's nudges therefore reach the entries:
`expm (rotz (90 deg ± 0.001 rad))` has a bound of 0.001 on its cosine
entries and only a second-order one on its sine entries. `expm (−B)` is
the inverse of `expm B` within the enclosures.

`transformBy R t` contracts `R` into every axis of `t`: `R v` for a
vector, `R P Rᵀ` for a matrix such as a covariance, and `R` on each of the
indices of a higher-rank tensor, so `transformBy R (a ⊗ b) == (R @ a) ⊗ (R
@ b)` and `transformBy R (transformBy S t) == transformBy (R @ S) t`. It
keeps `t`'s dimension and display unit; a number (rank zero) is returned
as it is. That every length of `t` is `n` cannot be written in the type
(§4.3), so it is checked when the call runs. Nor can "along every axis"
be said over axis sets (§3.9), so `R` has anonymous axes: a chart's
rotation, along two named sets, goes through the typed forms instead,
`rotateVec r v` (`r @ v`) and `rotateCov r p` (`r @ p @ rᵀ`) in `linalg`.

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
forall n m s d. Tensor (n : m : n : s) d -> Tensor (m : s) d
> :type \t -> permute [2, 0, 1] t
forall n m k s d. Tensor (n : m : k : s) d -> Tensor (k : n : m : s) d
> ([1, 2; 3, 4] m)._.0
[1, 3] m
> :type \m -> m._.0
forall n m s d. Tensor (n : m + 1 : s) d -> Tensor (n : s) d
> :type \t -> t._._.2
forall n m k s d. Tensor (n : m : k + 3 : s) d -> Tensor (n : m : s) d
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
forall d d1 n. (Num -> Num d -> Num d1) -> Vec n d -> Vec n d1
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
result's dimension from the function's type, and gives the result no display
unit of its own.

**Mapping is lazy, its dimension typed.** `vmap`, `vzipWith` and `timap` read
the result's dimension off their own type as instantiated where they are used
(§8), never off a component: `(vmap (\x -> 1/x) [0, 2]).1` is `0.5`, since
the division by zero in the other component is never forced, and a map over
an empty tensor has the dimension the function gives, `vmap (\x -> x * m)
(noise 0)` is `Vec 0 m` and `dot` of it with itself `0 m^2`. Inside a
polymorphic function the dimension is the caller's, passed as a type-level
argument. `vimap` stays the vector form with a scalar position; `timap` is the
general one. A diagonal mask:

```
> timap (\i x -> if i.0 == i.1 then x else 0) [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
[1, 0, 0; 0, 5, 0; 0, 0, 9]
> timap (\i x -> i.0 * x) [10, 20, 30]
[0, 20, 60]
> :type timap
forall s d d1. (Vec (rank s) -> Num d -> Num d1) -> Tensor s d -> Tensor s d1
> let diag t = timap (\i x -> if i.0 == i.1 then x else 0) t
> :type diag
forall n m s. Tensor (n : m : s) -> Tensor (n : m : s)
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
rotz t @ [1, 0, 0] km
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
approximation an extended Kalman filter makes. Only the remainder from bounded
inputs is a rigorous bound. Discarded statistical corrections are carried as
sizes and judged against the σ (§3.2); covariance summaries refuse marked
results.

There is no "reading" to choose: each nudge knows its kind. `±` contributes to the
bound, `±σ` to the covariance, and the printing, comparison, budget and covariance
rules all consult the kind.

**Correlated inputs are ordinary linear algebra.** A full 6×6 state covariance `P`
enters as its square-root factor `L` with `P = L Lᵀ`, split into homogeneous blocks:

```
let e = gauss 6
let r = r0 + Lr @ e           -- Lr : Mat 3 6 m
let v = v0 + Lv @ e           -- Lv : Mat 3 6 (m/s)
```

For the single-vector case `v ±σ P`, with `P : Mat n n (d^2)` the covariance
matrix, is `v + cholesky P · gauss n`: one statistical nudge per component,
identified by the definition site like every `±`, so two identical
declarations are independent and `#label` shares one. A bound has no covariance,
so `v ± P` with a matrix is a type error.

**Getting covariance out.** `covariance v : Vec n d -> Mat n n (d^2)` is an
ordinary function on a homogeneous vector, exact in the coefficients, and
`cholesky : Mat n n (d^2) -> Mat n n d` is its inverse on positive-definite
matrices (it fails with a domain error when a pivot's enclosure reaches zero).
Both `cholesky` and `v ±σ P` read only the lower triangle, so they first
check that the matrix is symmetric: every pair `P.i.j`, `P.j.i` must be
established equal. Unequal and undecidable pairs are refused by their entries.
`cholesky [1, 100; 0, 1]` fails with "cholesky needs a symmetric matrix:
entries .0.1 and .1.0 differ", and `[0, 0] ±σ [1, 100; 0, 1]` with "±σ
needs a symmetric covariance: …". Overlapping enclosures alone do not prove
symmetry; use the same uncertain value for both entries.
The REPL view `:covariance e` prints the covariance of a vector, or the variance
of a number, followed by the **bound box**: each component's rigorous radius
from the bound nudges, which has no variance and is reported beside it:

```
> :covariance [cos t, sin t, 0] km        -- t = 45 deg ± 0.001 rad
covariance [0, 0, 0; 0, 0, 0; 0, 0, 0] km^2
bound box [0.00071, 0.00071, 0] km
```

**Between two vectors.** `crossCovariance a b : Vec n d1 -> Vec m d2 -> Mat n
m (d1*d2)` is the same sum over the statistical nudges the two vectors
share: with `cᵢ` the coefficients of `aᵢ` and `c'ⱼ` those of `bⱼ`, entry
`(i, j)` is `Σ_k cᵢₖ c'ⱼₖ`. It is exact, its dimension is the product of the
operands', and it takes its display unit from both as `*` does (so
`crossCovariance r v` of a `km` and a `km/s` vector prints in `km^2 s^-1`).
`covariance v` is `crossCovariance v v` (one kernel computes both;
`covariance` stays a primitive, so no stored term changes hash, and keeps
printing in base units), and `crossCovariance v u` is `transpose
(crossCovariance u v)`. Two vectors with no statistical nudge in common
give zeros, and a shared *bound* nudge contributes nothing, since a bound
has no covariance:

```
> let e = gauss 2
> let r = [e.0 + 2 * e.1, 3 * e.0] m       -- coefficient rows (1, 2), (3, 0)
> let v = [e.1, e.0 - e.1] m/s             -- coefficient rows (0, 1), (1, -1)
> crossCovariance r v
[2, -1; 0, 3] m^2 s^-1
> crossCovariance ([1, 2] m ±σ 1 m) ([3, 4, 5] s ±σ 1 s)
[0, 0, 0; 0, 0, 0] m s
```

For a pair `(r, v)` the joint 6×6 has mixed units, which no homogeneous
matrix holds; it is the record of its three blocks (§3.7), and `:covariance`
on a pair of vectors prints them, labelled by the record's fields, followed
by the two bound boxes as a pair:

```
> :covariance (r, v)
rr [5, 3; 3, 9] m^2
rv [2, -1; 0, 3] m^2 s^-1
vv [1, -1; -1, 2] m^2 s^-2
bound box ([0, 0] m, [0, 0] m s^-1)
```

The blocks are `linalg.jointCovariance (r, v)`'s fields, computed by the same
kernel; `:covariance` does not look the name up, so it works after `:unuse
linalg` or with a root `jointCovariance` of the user's. Anything else that is
not a number or a vector is refused with "covariance: a number, a vector, or
a pair of vectors".

`:budget` and `:covariance` are two projections of one nudge set: budget sorts
`|cᵢ|` within each kind, covariance sums `cᵢ cᵢᵀ` over the statistical kind. A
correlation matrix is a trivial third.

---

### 3.6 Points and charts: affine quantities

Some quantities are **points**, not amounts: a temperature, an instant, an
electric potential, a position. Two points can be subtracted, giving the
amount between them, and an amount can be added to a point, giving another
point; but two points have no sum and a point has no double. Everything in
§3.2 to §3.5 is about amounts, which form the vector space `Num δ`. Points
form an *affine space* over it, and the language gives them their own type,
`Point c`, typed by the *frame* `c` they are written on (§3.10, part F), and
their own two operators, so that the arithmetic of points can never be
confused with the arithmetic of amounts, in the same way that the products
of §3.3 each have one symbol and one type.

| written | type | meaning |
|---|---|---|
| `p .- q` | `Point c → Point c → Diff c` | the amount from `q` to `p` |
| `p .+ v` | `Point c → Diff c → Point c` | the point `v` beyond `p` |
| `p == q`, `p < q` | `Bool` | points of one frame compare |
| `p + q`, `k * p`, `p + v` | type errors | points have no sum, no multiple; use `.+` |

`.-` reads "from", and `.+` and `.-` sit at the precedence of `+` and `-`.
`p .+ -v` is the point `v` before `p`. The one legitimate "sum of points",
the weighted mean, is `q .+ (p .- q) / 2`. `Diff c` is the amount type of
the frame's space, `Num K` for a temperature (§3.10, F4).

**Spaces and charts.** A point lies in a *space*, declared with the type of
its amounts, and is written and printed on a *chart* of it: a step unit and
an origin, given against the space's base (origin zero, the base unit as
step) or against a parent chart (§3.10, F2, F10):

```
space ITS90 = Num K                     -- in the library's temperature
unit  deltaC = K                        -- the Celsius step is the kelvin
unit  deltaF = 5/9 * 1 K                -- the Fahrenheit step
chart kelvin on ITS90                   -- the absolute scale
chart degC   on ITS90 at 273.15 K       -- 0 °C is 273.15 K from absolute zero
chart degF   on ITS90 at 459.67 deltaF step deltaF
chart degR   on kelvin step deltaF      -- Rankine: kelvin rescaled
chart J2000  on TT at 2451545 day step day   -- an epoch in Terrestrial Time
```

A chart declaration names a chart value and, when it is on a space or
gives an origin, a *frame*, a type (§3.10, F3); a chart with a step alone is
a rescaling and shares its parent's frame. The quantity rule accepts a
chart after a literal: `20 degC` is `pointOn degC 20 : Point degC`, the
point twenty steps up the chart from its origin, held as `20 K` above
degC's origin. `°C` and `°F` are the unicode spellings of `degC` and
`degF`. A difference carries the step unit of the chart its operands were
written on, so `77 degF .- 68 degF` is `9 deltaF`; `20 degC .+ 5 K` and `20
degC .+ 9 deltaF` are both `25 degC`. Points on two frames do not mix:
`20 degC .- 68 degF` is refused, "points on degC and degF: convert one with
`to`", and `p to degF` re-expresses a point on another chart of its space;
Rankine and kelvin are one frame, so `491.67 degR .- 0 kelvin` is `273.15 K`
with no `to`. A chart's step and origin may themselves be approximate, in
which case a point written on it carries their nudges like any other value.

**A step must be invertible.** A point prints with its step divided out
(F6), so a chart whose step may be zero has no coordinates: every point on
it would be the origin, and `1 c == 2 c` would hold. A step whose enclosure
reaches zero, exactly zero or uncertain across it (`step fuzz` with `unit
fuzz = 0 m ± 1 m`), is refused when the chart is used, naming it: "chart
collapsed has no invertible coordinates: its step is zero". A chart on such
a chart inherits the refusal, which names the parent. A **negative step** is
allowed and reverses the chart's direction: with `unit back = -1 m`, `chart
flipped on origin step back` writes `3 flipped` for `-3 origin`, and `(3
flipped) .- (1 flipped)` is `2 back`, that is `-2 m`.

**Printing.** A point prints as its coordinates on the chart it was written
on, the step divided out, followed by the chart's name: `25 degC`, `2451545
J2000`. Points are the one place a display offset is needed, and the only
place one is allowed: a *unit* is always a factor (§3.2.12), which is why
Celsius could never be a unit.

**Why a type and not a cleverer unit.** `20 °C + 5 °C` reads as 25 °C if the
second is a rise and as nothing if it is a temperature; written with a
factor-and-offset "unit" it silently becomes `298.15 °C`. The point/amount
distinction is the information the arithmetic needs, and it is the same
distinction as instant/duration, position/displacement, potential/potential
difference and absolute/gauge pressure. One type covers them all.

**Points over vectors.** A space may be of vectors, `space GCRS = Vec 3
m`, with base axes of its own (§3.10, F2). `chart site on GCRS at [100,
200, 0] m` is a frame; `[1, 2, 3] site` is the point with those coordinates
on it, `:type [1, 2, 3] site` is `Point site`, `p .- q` a displacement `Vec
GCRS m` along the base axes (a translated chart's axes are its
parent's), `p .+ v` moves a position, `p.0` is its first coordinate, the
amount `1 m`, and `p to eci` re-expresses it on another chart of the space.
A chart may also name a parent chart, `chart antenna on site at [2, 0, 1]
m`, and turn its axes, `by B` (§3.8).

### 3.7 Mixed dimensions

An orbit determination state is a position and a velocity, and the matrices
a filter needs over it, the covariance `P`, the state transition `Φ`, the
measurement matrix `H` and the gain `K`, have entries of several dimensions:
`P` has `m^2` in one corner, `m^2/s^2` in the other and `m^2/s` between.
Tensors are homogeneous (§3.3), so such a matrix is not a value. There are
two routes. Route B is built; route A is recorded so that it can be built
later without re-deriving it.

#### 3.7.1 Route A: Hart's dimensioned matrices (the escalation path)

G. W. Hart (*Multidimensional Analysis*, 1995) characterises the matrices of
quantities that linear algebra can work with. The rules:

- **Well formed.** An `m × n` matrix of quantities is well formed (Hart's
  "multipliable") when its dimensions factor as `dim Aᵢⱼ = rᵢ · cⱼ` for a
  *row dimension vector* `ρ = (r₀, …, r_{m-1})` and a *column dimension
  vector* `γ = (c₀, …, c_{n-1})`. The factoring is unique up to moving a
  constant between them (`rᵢ·k`, `cⱼ/k`), so the **canonical form** pins
  `c₀ = 1`, which makes `rᵢ = dim Aᵢ₀`.
- **Literals.** A literal is admitted when its dimensions factor, and refused
  otherwise: `[[1 m, 1 s], [1 s, 1 m]]` would need `r₀c₀ = m`, `r₀c₁ = s`,
  `r₁c₀ = s` and so `r₁c₁ = s²/m`, not `m`.
- **Product.** `A · B` with `A = (ρ_A, γ_A)` and `B = (ρ_B, γ_B)` is defined
  when `A`'s column vector times `B`'s row vector is one constant dimension,
  `c_Aₖ · r_Bₖ = κ` for every `k`, so that the terms of each inner sum agree;
  the result is `(ρ_A · κ, γ_B)`.
- **Transpose.** `Aᵀ` swaps the vectors: `(γ, ρ)`.
- **Inverse.** A square `A = (ρ, γ)` has `A⁻¹ = (1/γ, 1/ρ)`: entry `(i, j)`
  has dimension `1/(cᵢ rⱼ)`, so that `A A⁻¹` has `rᵢ/rⱼ`.
- **Determinant.** `det A` has dimension `Π rᵢ · Π cⱼ`, every term of the
  Leibniz sum having one factor from each row and each column.
- **Identity.** The identity that `A A⁻¹` gives is `(ρ, 1/ρ)`: dimensionless
  only on the diagonal, and a plain dimensionless `I` only when `ρ` is
  constant.
- **Vectors.** `Vec n d` embeds as the `n × 1` case with all rows `d` and
  the single column `1`; a homogeneous `Mat m n d` is `((d, …, d), (1, …, 1))`.

What building it takes: a type `DMat m n ρ γ` whose `ρ` and `γ` are
type-level lists of dimensions of lengths `m` and `n`, a new kind, unified
element by element by Kennedy's algorithm (§4.4) with variable tails the way
shapes are (§4.1); `encType` tags for it in `data` declarations (§6.1); a
second typing rule for every tensor primitive (`+`, `*`, `·`, `transpose`,
`inverse`, `det`, the literals, projection, slicing); and a printer that
gives each entry its own unit instead of factoring one out (§3.2.10).
Estimated at several agent-weeks, and every one of those pieces touches
inference, lint or the hash.

#### 3.7.2 Route B: blocks (built)

The state is a tuple of homogeneous vectors, `(r, v)` with `r : Vec n d1`
and `v : Vec n d2`, and every matrix over it is a record or tuple of
homogeneous blocks. Hart's factoring says why that is always possible: group
the rows and the columns of a well-formed matrix by equal dimension, and
each block of the grouping is homogeneous. The claim this route rests on:

> Every intermediate of a Kalman filter over a state that is a tuple of
> homogeneous vectors, measured by a homogeneous vector, is itself
> homogeneous, or a tuple or record of homogeneous blocks.

`Cov(xₐ, x_b)` has dimension `dₐ d_b`; a block `∂x'ₐ/∂x_b` of `Φ` has
`d'ₐ/d_b`; a block of `H` has `d_z/d_b`; `S = H P Hᵀ + R` has `d_z²`; a
block row of `K = P Hᵀ S⁻¹` has `dₐ/d_z`; and `(I − K H) P` has `P`'s
blocks again. Each is one dimension per block.

The library (§7.7) holds the two-block case, under `linalg`:

```
data Cov2 n d1 d2 = Cov2 {rr :: Mat n n (d1^2), rv :: Mat n n (d1*d2), vv :: Mat n n (d2^2)}

jointCovariance (r, v)    = Cov2 {rr = crossCovariance r r, rv = crossCovariance r v, vv = crossCovariance v v}
propagateCov2 (Φ_rr, Φ_rv, Φ_vr, Φ_vv) p                       -- Φ P Φᵀ
innovationCov2 h_r h_v p r_meas                                 -- S = H P Hᵀ + R, H = [H_r | H_v]
gain2 h_r h_v p s_inv     = (k_r, k_v)                          -- K = P Hᵀ S⁻¹
updateCov2 (k_r, k_v) h_r h_v p                                 -- (I − K H) P
```

The fourth block of `P` is `transpose p.rv`. With `P = [A, B; Bᵀ, C]` and
`Φ = [F₁₁, F₁₂; F₂₁, F₂₂]`, the block formulas, each derived by multiplying
the blocks out and each checked in the tests against the covariance read
directly off the affine forms, are

```
rr' = F₁₁ A F₁₁ᵀ + F₁₂ Bᵀ F₁₁ᵀ + F₁₁ B F₁₂ᵀ + F₁₂ C F₁₂ᵀ
rv' = (F₁₁ A + F₁₂ Bᵀ) F₂₁ᵀ + (F₁₁ B + F₁₂ C) F₂₂ᵀ
vv' = (F₂₁ A + F₂₂ Bᵀ) F₂₁ᵀ + (F₂₁ B + F₂₂ C) F₂₂ᵀ
S   = H_r A H_rᵀ + H_r B H_vᵀ + H_v Bᵀ H_rᵀ + H_v C H_vᵀ + R
K_r = (A H_rᵀ + B H_vᵀ) S⁻¹          K_v = (Bᵀ H_rᵀ + C H_vᵀ) S⁻¹
rr⁺ = A − K_r (H_r A + H_v Bᵀ)    rv⁺ = B − K_r (H_r B + H_v C)    vv⁺ = C − K_v (H_r B + H_v C)
```

`propagateCov2` forms the block rows of `Φ P` first, so `rr'` is computed
as `(F₁₁ A + F₁₂ Bᵀ) F₁₁ᵀ + (F₁₁ B + F₁₂ C) F₁₂ᵀ`, the same sum.
`updateCov2` writes `H P` as `(P Hᵀ)ᵀ`, `P` being symmetric, because
`h_r @ p.rr` with nothing else to fix `h_r`'s rank would default it to a
vector (§4.2), while `transpose h_r` makes it a matrix. The record keeps only
`rv⁺`; its mirror `Bᵀ − K_v (H_r A + H_v Bᵀ)` equals `transpose rv⁺` exactly
for the gain `gain2` computes, and the scenario test checks that too. The
matrix products are `@` (`·`), never `*`, which is the tensor product (§3.3).

`:type` prints (the variable names are inference's, so `d` and `d1` are
not the record's `d1` and `d2`):

```
jointCovariance : (Vec n d, Vec n d1) -> Cov2 n d d1
propagateCov2   : (Mat n m (d1*d2*d3/d^2), Mat n m (d1*d3^2/d^2), Mat n m d2, Mat n m d3) -> Cov2 m (d/d2) (d/d3) -> Cov2 n (d1*d3/d) d
innovationCov2  : Mat n m d -> Mat n m d1 -> Cov2 m (d1*d2/d) d2 -> Mat n n (d1^2*d2^2) -> Mat n n (d1^2*d2^2)
gain2           : Mat n m d -> Mat n m d1 -> Cov2 m (d1*d2/d) d2 -> Tensor (n : s) d3 -> (Tensor (m : s) (d1^2*d2^2*d3/d), Tensor (m : s) (d1*d2^2*d3))
updateCov2      : (Mat n m d, Mat n m (d1^2/d2)) -> Mat m n (1/d) -> Mat m n (d2/d1^2) -> Cov2 n (d*d2/d1) d1 -> Cov2 n (d*d2/d1) d1
```

All five are polymorphic in both state dimensions; none works only for
particular `d1`, `d2`. `propagateCov2` is the most general it can be: `Φ`
may change both dimensions and the length (input `Cov2 m D₁ D₂`, output
`Cov2 n E₁ E₂`, with `Φ_rr : E₁/D₁`, `Φ_rv : E₁/D₂`, `Φ_vr : E₂/D₁`,
`Φ_vv : E₂/D₂`). Read with the measurement's dimension `d_z`,
`innovationCov2` has `h_r : d_z/D₁`, `h_v : d_z/D₂` and `S : d_z²`.
`gain2` takes `s_inv` on the right of `@` only, so it accepts any tensor
whose first axis has the measurement's length; with a matrix `S⁻¹` it gives
`k_r : D₁/d_z` and `k_v : D₂/d_z`, the dimensions `updateCov2` asks for.

A zero block needs its dimension: `Φ_vr` of the constant-velocity `Φ =
[I, Δt I; 0, I]` is `1/s`, written `[0, 0, 0; 0, 0, 0; 0, 0, 0] s^-1`,
and a range measurement's `H_v` is `[[0, 0, 0]] s`; a bare dimensionless
zero would force `d1 = d2`. The scenario in §12 writes its own `eye`, since
the library has no `identity` yet.

Two smaller costs: the field names `rr`, `rv`, `vv` are labels in `linalg`
(`linalg.rr`), and a field is looked up by its name alone (§2.3), so a root
record with a field `rr` shadows the library's as any root name does
(§7.7): after `data Foo = Foo {rr :: Num}`, `p.rr` on a `Cov2` is refused
with "constructor Foo does not belong to Cov2 …". The library's own
definitions are unaffected, being terms by hash. Field completion after a
dot offers the three names too.

**The escalation signal.** Route B stops being the cheaper one when a
filter needs block formulas beyond 2×2 blocks (a state of three or more
vectors of different dimensions, where `Cov3` and its six blocks, or a
general n-block form, would be needed), or the inverse of a single matrix
of mixed dimensions: a measurement vector of mixed dimension (range and
range rate together) makes `S` itself a 2×2 block matrix, whose inverse is a
Schur-complement formula over the blocks. When either appears in real use,
route A is the next step, and its rules are above.
### 3.8 Charts: frames with an orientation (the tree, constant orientations and moving charts built)

A chart (§3.6) has three parts: a step unit, an origin and an orientation.
With the orientation the same construct describes a temperature scale, a
surveyed site, an orbital frame and a rotating planet; a chart on a space
of numbers has no axes to turn, and nothing in §3.6 changes for it.

**The one representation.** A chart over a space of `Vec n δ` is a value of
three fields: the step (a unit of the amount space), the origin (an amount
from its parent's origin), and a list of *generators* `B`, each an
antisymmetric `Mat n n` that is the oriented plane of rotation with the
angle as its magnitude (a bivector, in Grassmann's terms). The axes of the
chart are those of its parent rotated by `exp B₁ · exp B₂ · …`; an
axis-aligned chart has no generators.

```
chart degC on ITS90 at 273.15 K                    -- a space, an origin
chart site on GCRS at [100, 200, 0] m              -- a space, an origin
chart lvlh on eci at r0 by B                       -- a parent, an origin, an orientation
chart pf   on eci by rotz Ω then rotx i then rotz ω            -- a sequence of turns
chart ecef t on eci by rotz (gmst t) spinning [0, 0, 1] * ω_e  -- moving
```

The statement is `chart name params… on parent [at origin] [step unit] [by B
[then B …]] [spinning ω]` (§3.10, F10).

Why the generator and not the matrix: `exp` of an antisymmetric matrix is
always a rotation, so there is nothing to check, and its inverse is
`exp (-B)`: the *generator* is inverted exactly, by negation, while the
matrices on either side are enclosures (`expm (rotz (90 deg)) @ [1, 0, 0]`
prints `[3.0e-24 ± 3.8e-24, 1.000…, 0]`), so a round trip through a turned
chart encloses the point it started from rather than equalling it. Inverting
a rotation stored as a matrix of enclosures by Gaussian elimination would be
the one place the affine arithmetic suffers (§3.3, `inverse`). The matrix
is computed once per chart value, when a conversion first needs it, by
Rodrigues' formula for a single plane and by the exponential series in
general, with the same rigorous enclosures as `sin` and `cos` (§3.2.3);
`mkRoot` and `mkChart` check `B + Bᵀ == 0` exactly, which holds for
anything built with `∧` and for every constructor in `linalg` (§3.3, which
notes the one exception: an angle with an inexact `±` radius).

**Every other description is a library function to a bivector**, so the
Euler, axis-angle and quaternion forms are sugar and carry their conventions
in their names:

```
rotz θ         = θ / 1 rad * (e2 ∧ e1)  -- rotx, roty likewise; the right-hand rule: rotz (90 deg) turns x toward y
axisAngle n θ  = dual (θ / 1 rad * (-n) / norm n)   -- 3D: the axis is the dual of the plane
rotation a b   = the bivector taking a to b, angle atan2 (norm (a × b)) (a · b)
fromQuaternion q = the logarithm of the rotor, for input only
```

An Euler sequence is not one bivector but several, applied in turn, and a
chart is turned by the sequence itself: `by rotz Ω then rotx i then rotz
ω` is the 3-1-3 sequence. `euler313 Ω i ω` in `linalg` is the composed
*matrix* `expm (rotz Ω) @ expm (rotx i) @ expm (rotz ω)`, for `@` and
`transformBy`, and is not a generator.

Euler angles have gimbal lock and twelve sequence conventions, so each
sequence is its own function; quaternions double-cover (`q` and `-q` are one
rotation), so they are accepted as input and never stored. The generator has
neither problem: one plane, one angle.

**A chart's orientation is a list of generators.** A composed rotation,
such as an Euler sequence, is not `expm` of any single bivector, so `by`
takes a list of generators applied in order, written with `then`: `by rotz
θ` is a list of one, and `by rotz Ω then rotx i then rotz ω` a list of
three. `then` is read as a separator in the chart statement only, after
`by` and outside brackets, and an `if` inside a generator keeps its own
`then`; the parser makes a list literal of the generators, so the
desugarer stays syntactic and the Core is `mkChart {F} {A} parent {} {}
{g₁, …} {}`, the empty lists the clauses not written (§4.3). Every element
is checked antisymmetric, the inverse is the list reversed with each
element negated, and nothing needs a matrix logarithm or an orthogonality
check on enclosures. The chart keeps its rotation `R = expm B₁ · expm B₂ ·
…` beside the generators, computed once per chart value when first used.

**Conversion.** `p to c` gives `p`'s coordinates on chart `c`: from its
own frame's `(o_F, R_F)` to the base and down, `R_c⁻¹ (o_F + R_F x − o_c) /
step_c`, components along `c`'s axes. A displacement converts by the
rotations alone, a point by rotation and translation. A tensor of any rank
converts by applying the rotation along every axis, so a covariance block
goes as `R P Rᵀ` (§3.7). Charts form a tree: a chart names the chart its
origin and axes are given in, and at the root a space (§3.10, F2), and `a
to b` goes up to the common ancestor and down, composing at the matrix
level since two rotations in different planes do not add as bivectors. A
chart's parent comes after `on`:

```
space GCRS = Vec 3 m
chart eci       on GCRS                                       -- the root for positions
chart perifocal on eci by rotz Ω then rotx i then rotz ω       -- rotated, same origin
chart site      on eci at [6378, 0, 0] km                      -- translated
chart antenna   on site at [2, 0, 1] m by rotz (30 deg)        -- relative to site
```

A chart on a space is given against the space's base (origin zero, base
axes, the base unit as step); the parent is a reference to a definition,
so the chart tree and the namespace tree are unrelated, and renaming a
chart changes nothing. None of this needs §3.7's route A: a rotation is
dimensionless and a chart has one dimension on every axis, so every
conversion stays homogeneous.

**The translated tree.** Each clause runs to the next clause word, so an
origin built with an operator needs no parentheses (`at r0 + r0`) and a
function applied to a chart may stand in it. `by` is a word in this
statement only, so `by B * pi / 6` keeps its whole expression and `let by
= 5` is a name everywhere else. The origin is an amount from the parent's
origin along the parent's axes, so `chart site on eci at [6378, 0, 0] km`
and `chart antenna on site at [2, 0, 1] m` put `[0, 0, 0] antenna` at
`[6378002, 0, 1] eci`: `[1, 2, 3] antenna to eci` is `[6378003, 2, 4] eci`
and converts back exactly, and `[1, 2, 3] antenna .- [0, 0, 0] site on
site` is `[3, 2, 4] m`. `:view` and `:edit` print `chart antenna on site at
[2, 0, 1] m`, a turned chart with its `by`, the generators joined by
`then`, and re-entering what they print gives the same hash.

**Turned charts.** Every chart keeps its *absolute frame*, its origin and
rotation from the space's base, so that no conversion walks the tree:

```
R_abs = R_parent_abs · expm B₁ · expm B₂ · …          -- I for a root; a chart with no by has its parent's
R_abs⁻¹ = … · expm (−B₂) · expm (−B₁) · R_parent_abs⁻¹  -- from the generators, never by inverting an enclosure
o_abs = o_parent_abs + R_parent_abs · a               -- a: the amount the origin is given at, along the parent's axes
```

The origin `a` is an amount with its own unit (`[7000, 0, 0] km`), not a
count of the parent's steps, so a translated chart is exactly what it was.
A point holds its coordinates on its frame with the step applied (§3.10,
F6), `step · c`; `p to c` maps them through the base, `o_abs + R_abs x`
up and `R_abs⁻¹ (· − o_abs)` down. With `chart eci on GCRS` and `chart
lvlh on eci at [7000, 0, 0] km by rotz (90 deg)`, lvlh's x axis is eci's
y: `[1, 0, 0] lvlh to eci` prints `[7000000.0000000000000…,
1.0000000000000000000…, 0] eci`, and `[7000000, 1, 0] eci to lvlh` prints
`[1.0000000000000000000…, 3.0e-24 ± 3.8e-24, 0] lvlh`. A round trip
encloses the point it started from, with bounds under `4 × 10⁻²⁴` for one
level of turning and `3 × 10⁻²³` for two, and is checked with `bound` or an
enclosure test, never `==`, which may answer "cannot decide".

*Displacements are along a frame's axes.* A point is held in its frame's
coordinates, so `p .- q` for two points on one frame is the difference of
their coordinates, exact, along the frame's axes: `[1, 2, 3] lvlh .- [0, 5,
0] lvlh` is `[1, -3, 3] m`, a `Vec lvlh m`, and `q .+ (p .- q)` is `p`.
Re-expressed along another chart's axes it turns by the rotations alone:
`([1, 2, 3] lvlh .- [0, 5, 0] lvlh) from lvlh to eci` encloses `[3, 1, 3]
m` (§3.10, F10).

*Tensors of higher rank.* `rotationOf c` (a primitive) is `R_abs`, whose
columns are `c`'s axes along the space's base axes; it is exactly the
identity for a chart that is not turned. Its type says so (§3.10, F5):
`rotationOf lvlh : Mat GCRS lvlh`, rows along the base, columns along the
chart. `v to c`, with `v` along the base axes, is `Rᵀ v`, and `v from c
to eci`, with `v` along `c`'s, is `R v`: `R` is orthogonal, so the
transpose of an entrywise enclosure of it is an entrywise enclosure of
`R⁻¹`. A covariance turns as `R P Rᵀ`, `linalg.rotateCov (rotationOf c)
p`, and `inChartCov2 c p` does each block of a `Cov2` (§3.7) so, since a
state's rotation is `R` on positions and velocities alike. `transformBy`,
which applies `R` along every axis at once, is for anonymous axes only.

A coordinate of a point, `p.0`, is an amount along its frame's own axis,
the step applied, on any chart (§3.10, F5). A turned chart's rotation is
computed once per value, and a definition's value is shared by every
reference to it in one evaluation, so a chart named in a hundred
conversions computes `expm` once per generator and direction.

**Moving charts.** A chart that moves is a function of an epoch to a
chart, and the epoch is a point on a time chart (`unix`, `J2000`). The
chart statement takes parameters exactly as `let f x = …` does, before
`on`, and a `spinning` clause:

```
chart spinner t on eci by rotz (w * (t .- t0)) spinning [0, 0, 1] * w
```

desugars to `\t -> mkChart {Frame} {Axes} eci {} {} {rotz (w * (t .-
t0))} {[0, 0, 1] * w}`, `Frame` and `Axes` the constructors of the frame
and axis types the declaration mints (§3.10, F3), inside the lambda, so
that `spinner t` has one frame and one axis set for every `t`; and the
*name* carries the chart flag. `spinning` is a word in this statement
only, like `by`. It takes a `Vec 3 (rad/s)` (a literal is dimensionless,
so a spin is written `[0, 0, 1] * w` or `[0, 0, 7.29e-5] rad/s`, not `[0,
0, w]`); the radian is stripped as `rotz` strips it, so the chart keeps
`Vec 3 (1/s)`, an angular velocity along the chart's *own* axes, relative
to its parent. A spinning chart with no `by` has an empty list of
generators and prints with no `by`. `:view spinner` prints `chart spinner
t on eci by rotz (w * (t .- t0)) spinning [0, 0, 1] * w`, the lambda's
parameters before `on`, and `:edit` reads back to the same hash.

*Applying one.* A chart declared with parameters is a *moving chart*, which
the resolver reads off its stored Core (a lambda), so a store reload keeps
it with no flag of its own. Where a chart goes, an application whose head
is a moving chart's name takes the chart at that instant: `p to spinner
t1`, `p to (spinner t1)`, `[1, 2, 3] (spinner t1)` and a parent `chart
station t on (spinner t) at [6378, 0, 0] km by roty (30 deg)`. A moving
chart's bare name where a chart is wanted (`p to spinner`, `[1, 2, 3]
spinner`, `on spinner` as a parent) is refused when desugaring, "`spinner`
takes arguments: apply it, as in p to (spinner t0)" (§3.10, F7), and a
point on it converts from a configuration named with `from`, `p from
(spinner t1) to eci`, never the one it was written with, which makes the
classic wrong-epoch mistake an error. An instant prints as it was applied,
`[1, 2, 3] (spinner (1000 unix))`, which reads back. A state is converted
by named library functions (below).

*Kinematics, composed through the tree.* A velocity seen from a moving chart
picks up transport terms, and a moving chart states its angular velocity,
since differentiating `exp B(t)` would need automatic differentiation we do
not have. Each chart value keeps, beside its absolute frame, its absolute
angular velocity `ω_abs` and the velocity of its origin `v_o_abs`, both
along the base axes, computed once per value when first used. With `a` the
amount the origin is given at along the parent's axes, `R` the chart's own
rotation `expm B₁ · expm B₂ · …`, `ω` its own spin along its own axes, and
`_p` the parent's absolute values:

```
o_abs   = o_p + R_p a
R_abs   = R_p · R
ω_abs   = ω_p + R_abs ω          -- ω = 0 without spinning; ω_p = 0 at a root
v_o_abs = v_o_p + ω_p × (R_p a)  -- origins are fixed relative to their parent
```

The velocity of a body at base position `p` with base velocity `v`, read
along chart `c`'s axes, and written back:

```
v_c = R_abs⁻¹ (v − v_o_abs − ω_abs × (p − o_abs))
v   = R_abs v_c + v_o_abs + ω_abs × (p − o_abs)
```

Three primitives read these fields: `spinOf : forall s (c : s). Chart c
-> Vec s (1/s)` is `ω_abs`, `originVelocityOf : Chart c -> Vec s (d/s)` is
`v_o_abs` (a space in metres gives `Vec s (m/s)`) and `originOf : Chart c
-> Vec s d` is `o_abs`, each along the space's base axes (§3.10, F5), the
first two over three axes and exactly zero when nothing here or above
spins. `R_abs⁻¹` is `v to c`: `R` is orthogonal, so the transpose of an
entrywise enclosure of it encloses its inverse.

*States, in `astro`.* `astro` is not used by default, so its field labels
never meet a user's (`:use astro` first):

```
data State t r = State {epoch :: Point t, pos :: Vec r m, vel :: Vec r (m/s)}
velocityIn c st =
  (st.vel - originVelocityOf c - linalg.cross (spinOf c) (st.pos - originOf c)) to c
stateFrom c t pc vc = let r = rotationOf c @ pc in
  State {epoch = t, pos = originOf c + r,
         vel = rotationOf c @ vc + originVelocityOf c + linalg.cross (spinOf c) r}
```

`pos` is the position as an amount from the space's base origin and `vel`
the velocity, both along the base axes: the velocity relative to the base,
the inertial frame. A state is typed by its epoch's frame and its space's
base axes (§3.10, part F, as built): `stateFrom lvlh (0 unix) …` is a
`State unix GCRS`, and `pc` and `vc` are along the chart's own axes,
`Vec lvlh m`, so `velocityIn` and `stateFrom` refuse a vector of another
frame. Their inferred types now express the space constraint; `:type`
prints `forall (s1 : Space (Vec 3 m)) (c : s1) c1. Chart c ->
State c1 s1 -> Vec c (m/s)`. `velocityIn c st` is that velocity relative
to `c`, along `c`'s axes; `stateFrom c t pc vc` is the inverse, a position
`pc` (an amount from `c`'s origin along its axes) and a velocity `vc`
relative to `c` to a state at epoch `t`. Both take a chart *value*, so a
moving chart is passed at the state's instant, `velocityIn (ecef st.epoch)
st`. The formulas are library code, so `:view astro.velocityIn` shows them.

*What the tests check* (`movingChartTests`): physics, not the formulas
echoed. A body fixed on `spinner t1`, with inertial velocity `ω × r`
computed in the test, has `velocityIn` enclosing `0`, and `stateFrom` gives
it `7000 km · w · [−sin θ, cos θ, 0]` by hand; a body at rest in the parent
turns backwards on the chart. `stateFrom` then `velocityIn` and the
position read back enclose what went in, on a chart turned, offset and
spinning under a spinning parent. A body fixed on `spinner` at `t1` and at
`t1 + 1 ms`: the forward difference of its positions differs from the
velocity `stateFrom` gives by `3.6460579499999995e-8 ± 2.9e-23` of the speed,
which is `ω δt / 2`, the centripetal term. Two levels: a station under the
spinning chart, turned and offset, has spin `ω` and origin velocity `ω × (R_p
a)` by hand, and a body fixed at it, moving with `ω × (p − o_eci)`, is at
rest relative to it; a dish spinning at 0.01 rad/s on the station agrees
with a central difference of positions to `4e-13 m/s` (each component under
`1e-11`), where a spin left out or not turned by `R` would be off by `0.01
m/s`. Nothing checks that a declared spin is the derivative of the
rotation it goes with: that is the author's to keep, and the finite
difference is how to check it.

*Uncertainty passes through.* An uncertain spin rate, `7.2921159e-5 rad/s
± 1e-10 rad/s`, gives a body 7000 km out a velocity with a bound of `7e-4
m/s` and one 14000 km out twice that.

**Uncertainty comes for free.** `gmst t` with an uncertain `t` gives an
enclosure for the angle, so `R` has affine entries and `R @ r` carries the
chart's uncertainty, correlated across components as always (§3.4). No part
of this design is about error; it inherits §3.2. With `by rotz (30 deg ±
0.001 rad)`, `[1000, 0, 0]` on the chart prints `[866.03 ± 0.53, 500.00 ±
0.87, 0] eci`, while the norm of its amount from the origin, `1000`
whatever the angle, has a bound of `5.4e-4`: the first-order terms cancel.

**Charts are affine; curvilinear coordinates are functions.** Polar and
spherical coordinates are not charts here: the map is nonlinear, its
coordinates have mixed dimensions (`r` in metres, the angles in radians), and
differences of polar coordinates are not displacements, so a `Point` on such
a chart would break the law `.-` exists to guarantee. They are ordinary
functions to a record of amounts, `toPolar v = Polar {r = norm v, theta =
atan2 v.1 v.0, …}`, and the affine arithmetic linearises them, so
`crossCovariance` of the result's components is the Jacobian-propagated
covariance with no extra machinery (§3.4, §3.7). Range, azimuth and
elevation from a station are `to` the station's chart, then such a function.

**What stays separate.** `unit` stays separate from `chart`, because a unit
is a basis element of a vector space and a chart puts coordinates on an
affine space, and that distinction is what refuses `20 degC + 30 degC`.
Per-axis units in one chart (x in km, z in m) are a basis with mixed
dimensions and wait on §3.7's route A.

**The pieces.**

- **The chart value** (`Metron.Eval.Chart`, the value constructor `VChart`)
  holds its step and the step's display unit, its origin as an amount from
  the space's base origin along the base axes, `parent :: Maybe Chart`
  (the parent chart's *value*, not a hash: a chart need not be named, and
  the definition's Core already refers to the parent's definition by
  hash), `generators` (antisymmetric `n × n` matrices, row-major, applied
  in order), the absolute frame (`rotation` and `rotationInverse`, lazy,
  `Nothing` when nothing here or above is turned), `spin` (its own angular
  velocity along its own axes, in s⁻¹), the absolute kinematics (`spinAbs`
  and `originVelocity`, lazy like the rotation, `Nothing` when nothing here
  or above spins), `frame` (the hash of the frame it is a chart of),
  `moving` (whether that frame's chart takes parameters), and `applied`
  (the arguments of the moving chart an instant came from, for printing
  only; `Eq` ignores them).
- **`mkRoot` and `mkChart`** (§3.10, F10) build it from its clauses, each a
  list of none or one, the generators any number. Each generator is a
  dimensionless `Mat n n` over the chart's own axes, checked `B + Bᵀ == 0`
  exactly, entry by entry as `Bⱼᵢ == -Bᵢⱼ` on the affine forms (an
  approximate angle times an exact bivector passes; a sum `Bᵢⱼ + Bⱼᵢ`
  would not, since slack never cancels), else "the generator of a chart
  must be antisymmetric: a bivector, such as rotz θ or a ∧ b". A `by`
  needs a parent: a turned chart names the chart its axes are turned from.
- **`rotationOf : Chart c -> Mat s c`**, the absolute rotation, exactly `I`
  for an unturned chart; `spinOf`, `originVelocityOf` and `originOf`
  (above). In `linalg`, `rotateVec r v` (`r @ v`), `rotateCov r p` (`r @ p
  @ rᵀ`) and `inChartCov2 c p`, a `Cov2` block by block.
- **`expm : Mat n n -> Mat n n`**, dimensionless, a rigorous enclosure:
  statistical inputs (including marked results with no surviving statistical
  coefficient) are currently refused. The bounded series does not yet
  propagate their statistical remainder. This restriction also applies to
  chart rotations evaluated through `expm`.
  Rodrigues for a single plane (any antisymmetric matrix when `n ≤ 3`, an
  exact one checked beyond), the exponential series with scaling and
  squaring otherwise (§3.3). `expm (-B)` is the inverse of `expm B` within
  the enclosures.
- **`transformBy : Mat n n -> Tensor s d -> Tensor s d`**, `R` applied
  along every axis (a vector gets `R v`, a matrix `R P Rᵀ`). The type cannot
  say that every length is `n`, so another length is refused when the call
  runs, "transformBy: every axis must have length n" (§4.3); nor can it say
  "every axis" over axis sets, so its matrix has anonymous axes.
- **In `linalg`**: `e1 e2 e3 : Vec 3`; `rotx`, `roty`, `rotz : Num rad ->
  Mat a a` (`rotz θ = θ / 1 rad * (e2 ∧ e1)`, since `a ∧ b` turns `b`
  toward `a`; `expm (rotz (90 deg)) @ [1, 0, 0]` encloses `[0, 1, 0]`);
  `dual`, the inverse of `⋆`; `axisAngle : Vec 3 d -> Num rad -> Mat 3 3`;
  `rotation : Vec 3 d -> Vec 3 d1 -> Mat 3 3`, the bivector taking `a` to
  `b`; `euler313 : Num rad -> Num rad -> Num rad -> Mat 3 3`, the composed
  matrix, not a bivector, its name saying the sequence. Every bivector they
  return is exactly antisymmetric (§3.3).
- **Printing.** A chart's type is `Chart c`, its frame (`Chart lvlh`,
  `Chart degC`); `:ls --charts` lists charts; `:view` and `:edit` print the
  statement with the clauses written, in the order `at`, `step`, `by`,
  `spinning`.

**Open.**

- *An Earth chart.* None is shipped, and that is the owner's decision to
  make separately: an Earth-fixed chart honest at the kilometre level
  needs precession and nutation (the equinox of date has moved about
  0.36° from J2000's by 2026, some 40 km at the equator), polar motion,
  and UT1 rather than UTC for the Earth's angle, and this tool promises
  honest bounds. The library ships the mechanism only; §12 defines a
  simple spinning Earth for illustration, with its accuracy stated.
- *Time scales.* `JD`, `MJD` and `J2000` are charts on `TT`, and `unix` on
  `UTC`, a space of its own (§3.10, F2). No chart joins them: the map
  between TT and UTC is a constant plus the leap seconds, an ordinary
  function over a leap-second table, which the library does not ship. UT1
  and TAI are not modelled.
- *Origins that move relative to their parent.* `v_o_abs` counts only the
  parent's spin: a chart whose origin is a function of its time parameter
  (`chart c t on eci at r t`) gets no velocity for that motion, which a
  declared origin velocity, as the spin is declared, would add.
- *A declared spin is not checked* against the rotation it goes with (it
  would need the derivative of `expm B(t)`).
- Whether `GCRS` and `eci` are library declarations (none is shipped yet: a
  user's `space GCRS = Vec 3 m` and `chart eci on GCRS` are a space and a
  root like any other).

**Axis sets.** Vectors typed by their axes are §3.9: a chart is an axis set
with an origin, and `p to lvlh` returns a `Point lvlh` whose differences
are `Vec lvlh m`.

### 3.9 Axis sets: named positions and index types (built through stage 3; stage 4 in part)

Two layers, the first a sugar and the second a type-system extension.

**Layer 1, named positions.** `axes x y z` declares labels for positions 0,
1, 2 in the current namespace, persisted as label lines like fields, moved by
`:rename`, resolved through scope. `v.x` desugars to `v.0`: the same Core and
the same hash as the numeric form, so `:view` prints whichever was written
and projection's static bound applies (`v.z` on a `Vec 2` is refused). It
works at any rank (`m.y.x` is row 1, column 0). `linalg` seeds `axes x y z`.

**Layer 2, axis sets as types.** Amounts carry the axes they are measured
along, so mixing components of two frames is a type error and a
displacement taken inside a frame prints along that frame's axes. The
decisions:

1. **An axis set is a static, type-level name.** §4.1 keeps terms out of
   types, so `Vec (ecef t)` cannot exist. A chart declaration with `by` or
   `spinning`, and a vector space (§3.10, F2), introduce one axis-set name; a
   moving chart has one axis set for all `t` (its axes turn, its identity
   does not). A plain length is the *anonymous* set of that size: `Vec 3` is
   `Vec (Anon 3)`. Two named sets never unify with each other, nor with an
   anonymous one.
   **The identity lives in the content, not the name** (decided by the
   owner). Two charts with the same body share a hash, and a stored value's
   type comes from its Core alone, so a frame carried on the name would be
   lost the moment a value is stored. As with the owner stamp of a `±`
   measurement (§3.2.4), the name enters the content: the desugarer mints,
   for each declaration that names axes, a hidden nominal axis type stamped
   with the full path, and passes its nullary constructor to the chart
   primitive; the primitive's scheme reads the axis set's hash from that
   argument as `contract` reads its literal positions. Persistence,
   printing by name and the re-hash on `:rename`/`:move` are the
   declared-type machinery's. The stamp's label kind is one no source
   declaration can produce, so a user's `data Lvlh = Lvlh` never collides. A
   moving chart mints inside its lambda body, so `ecef t` has one axis set
   for every `t`.
2. **`card` and constraints.** An axis set has a size, `card lvlh = 3`,
   `card (Anon k) = k`. `rank s` counts axis sets as it counts lengths.
3. **Matrices carry a row and a column axis set.** This is where the safety
   comes from. `rotationOf lvlh : Mat GCRS lvlh` (rows along the space's
   base axes, columns along lvlh's), and `@` requires the contracted axes
   to match, so `rotationOf lvlh @ v` with `v : Vec lvlh` is a `Vec GCRS`,
   and applying the wrong rotation is a type error. Route A for mixed
   dimensions (§3.7) needs the same row and column machinery for
   dimensions; the two should share it, but stay separate designs.
4. **Points are typed by their frame and stored in their chart's
   coordinates** (decided by the owner; §3.10, F4, F6). `[1.5, 2.25, 3]
   lvlh : Point lvlh`, held as the three numbers `1.5, 2.25, 3` and the
   chart, so arithmetic inside a frame is exact, `p.0` is `1.5` along
   lvlh's x axis, and `q .- p` for two points on one chart is a `Vec lvlh
   m`. A point on a moving chart is held in that chart's coordinates too,
   so a point fixed on a moving body (a ground station) is a constant;
   converting it out needs the chart's arguments, its time and any other
   parameters, so the wrong-epoch mistake is a missing argument rather
   than a silent error. Points on different frames compare or subtract only
   after an explicit `to`, which is the typed conversion between them.
   Scalar points (`Point degC`) have no axes.
5. **Literals are polymorphic in their axes** (decided by the owner). An
   unannotated literal vector gets a fresh axis variable, as an untyped
   numeric literal does in Haskell, so its frame comes from where it is used:
   `p .+ [1, 0, 0] m` is along `p`'s axes, `[1, 0, 0] m + v` along `v`'s. A
   literal has no frame until it is used, so this is not a frame mix-up.
   `v to c` re-expresses a vector that already has a frame along another
   chart's axes, which is a rotation and stays visible. The restriction is
   on named values: functions generalise over axis variables as usual (`let
   shift p = p .+ [1, 0, 0] m` is "the same frame as `p`"), but a named
   non-function value does not keep a free axis variable. If nothing in
   its definition fixes its frame, its axes default to anonymous, so `let
   offset = [0, 0, 2] m` cannot silently be a body-frame offset in one use
   and an inertial one in another; it meets a frame through `to` or a
   signature (`offset :: Vec body m`), and the first use against a frame
   says so. An ascription narrows and never relabels (§4.8).
6. **`forall` is required, with kinds on binders** (decided by the owner).
   A signature or an ascription that has type variables binds them with
   `forall`; every other name in a type is a name and resolves like one, so
   a new unit called `d` cannot change the meaning of an existing
   signature. A binder can carry a size: `cross :: forall (a : 3) d d1. Vec
   a d -> Vec a d1 -> Vec a (d*d1)` reads "any three-axis frame, the same
   one throughout". `offset :: forall a. Vec a m` is the deliberate opt-in
   of decision 5. A `forall` scopes its variables over the body, so an
   ascription inside refers to the signature's frame. `:type`, `:ls` and
   `:view` print the `forall`, so what is printed can be pasted back; `:ls
   : type` queries stay implicit, being search patterns; `data` parameters
   are already explicit. §4.8 has the rules in full.
7. **The base axes are named** (decided by the owner; §3.10, F2). A vector
   space names its base axes after itself; a root chart has its space's
   axes, a translated child shares its parent's, and a rotated child names
   its own. Two root charts on one space (`eci`, a lab bench) have one set
   of axes; roots on two spaces never meet. Literals take their frame from
   use (decision 5); a named value with no frame of its own is anonymous
   and meets a frame through `to` or a signature.
8. **Encoding.** The anonymous set of size `k` encodes byte for byte as a
   bare length `k`; a named set or an axis variable is a tag of its own
   (§6.1).
9. **Existing primitives.** `slice`, `contract`, `permute` and `timap` move
   or drop axis sets as they move or drop lengths; `cross`, `norm`, `dual`
   and the rotation constructors generalise over `a` with `card a ~ 3`
   (stage 4, below); the `Cov2` blocks are `Mat a a (d^2)`, `Mat a b
   (d*d1)`. `transformBy` stays over anonymous axes, since no type says
   "every axis" over axis sets at any rank; `rotateVec` and `rotateCov` are
   its typed forms.

```
cross       : forall (a : 3). Vec a d -> Vec a d1 -> Vec a (d*d1)
norm        : Vec a d -> Num d
rotationOf  : Chart c -> Mat s c                     -- rows along the space's base axes, columns along the frame's (§3.10)
p to c      : Point c -> Chart c1 -> Point c1        -- one space; a chart with parameters is applied, its source named with from
v to c      : Vec s d -> Chart c -> Vec c d          -- re-express a vector along a chart's axes: a rotation, visible
q .- p      : Point c -> Point c -> Diff c           -- one frame in, its axes out (Diff lvlh = Vec lvlh m)
v.0         : Vec a d -> Num d                       -- a has at least one axis
v.x         : Vec a d -> Num d                       -- x one of a's axis labels (layer 1)
```

**Stages.** 1, axis sets in shapes, all anonymous; 2a, required `forall`;
2b, named axis sets for amounts; 3, units, spaces and frames (§3.10); 4,
the library generalised over axis sets. Stages 1 to 3 are built. Of stage
4, `cross`, `norm`, `rotx`, `roty`, `rotz`, `Cov2` and `timap` are
generalised; `rotation`, `dual` and `axisAngle` print free axes of their
own (`rotation : forall d d1 (a : 3) (b : 3). Vec 3 d -> Vec 3 d1 -> Mat a
b`), and §12's sessions are to be rewritten to the typed form.

**As built.**

- **An axis set is a length and a name slot.** A shape position is a length
  (a literal, `n + k`, `rank s + k`) and a name slot beside it: anonymous, a
  named set (the hash of what declares it), or an axis variable, of the
  kind `Axis` (§4.1). `Vec (Anon 3)` is the position `3` with an anonymous
  slot. The `card a` of decision 2 is the length beside the slot, so there
  is no `card` function and no `card` constraint: `card a ~ 3` is the
  literal `3` beside an axis variable `a`. `(length, axes)` below is not
  syntax.
- **The slot unifies syntactically.** Anonymous with anonymous, a name with
  itself, a variable with any slot (with the occurs check); any other pair
  fails with a message naming both, "the axes of lvlh against anonymous
  axes", "the axes of lvlh against the axes of GCRS". Lengths are unified
  first, so a mismatch of lengths reports as one. Lint matches a slot as it
  matches a length: an instance substitutes axis variables too, and its
  type application is capture-avoiding.
- **A written length variable is a whole axis set.** In a signature, a
  `data` declaration or a `:ls` query, a lowercase variable in a length
  position elaborates to a length variable and a companion axis variable,
  both quantified; a literal length is anonymous, and so is `rank s`, as
  an index's positions are numbers. A `data` parameter of kind length
  gains a companion axis parameter, numbered after the written ones and
  never printed, and its arguments are the axes of the length they go
  with. A sized binder is its literal length beside an axis variable of its
  own. Signatures are numbered in order of appearance, so a signature and
  the text it prints as are one scheme.
- **The primitive schemes say which axes must match** (decision 9).
  Elementwise operators share the whole shape; `outer` carries axes through
  `Append`; `dot` contracts the left's last position against the right's
  first, one length and one axis variable between them. `transpose : Mat
  (n, a) (m, b) -> Mat (m, b) (n, a)` and `inverse : Mat (n, a) (n, b) ->
  Mat (n, b) (n, a)` swap rows and columns with their axes; `cholesky`
  keeps both; `det` is over two axis sets of one size, `expm`, `wedge` and
  `covariance` over one, `star` over one set beside the literal `3`;
  `crossCovariance : Vec (n, a) -> Vec (m, b) -> Mat (n, a) (m, b)`; `norm`
  and `indices` keep the argument's. `contract`, `permute` and `slice` move
  or drop a position's axes with its length, `contract`'s pair sharing
  both; `timap`'s index `Vec (rank s)` is anonymous.
- **`forall`** (decision 6; §4.8). `forall` (or `∀`), binders, `.` at the
  head of a signature's or an ascription's type; a binder is a name or a
  sized `(a : 3)` (§2.7), and `forall` is a keyword. Every variable of a
  signature or an ascription is bound; an unknown lowercase name is refused
  ("unknown name `x` in a type; bind it with forall if it is a variable").
  A binder shadows a unit, base unit or type of its name within its type
  (and a signature's, within its body's ascriptions), never in an
  expression, so the printer uses plain names and skips one only when the
  same type prints that base symbol (`forall s1 d. Tensor s1 d -> Tensor s1
  (s*d)`). A signature given with its definition scopes its variables over
  the body's ascriptions; when one names them, the body is checked wrapped
  in the signature, with the shared variables in a range of their own, and
  the signature checked again on the result. `:type`, `:ls` and every
  written-back signature (`:edit`, `:export`, `:scratch`, the `sig` line)
  print the `forall`, sized binders sized, `forall (a : 3) d. Vec a d ->
  Vec a d`, and read back as themselves; errors, `:lint` and `:core` do
  not print it. `:view` shows a term or a declaration, never a scheme.
- **Minted axis types.** Entering a chart with `by` or `spinning`, or a vector
  space, mints a nominal type: no parameters, one constructor with no
  fields, labelled `Axes "full.path"`, a label kind no source `data` has
  (§6.1), so `data Eci = Eci` never equals a chart's axes. It is stored
  like a declared type and prints as its frame's or space's name; types
  and terms are separate namespaces, so `lvlh` the chart and `lvlh` its
  axes coexist, and `:export` leaves the axes out, since the declaration
  mints them again. The desugarer passes its constructor to `mkRoot` or
  `mkChart`; a chart with neither shares its parent's axes and mints
  none. Two charts with one body are two axis sets and two hashes. A chart
  moved by `:rename` or `:move` takes its axes with it (their stamp is its
  path), and a chart redefined as no chart drops its axes' name.
- **Literals and named values** (decision 5). A literal's positions, and a
  stack's new one, get fresh axis variables, carried in Typed Core
  (`TLit`, `TPack`), so `p .+ [1, 0, 0] m` takes `p`'s axes. A named value
  that is not a function has its free axes anonymous: a local `let` at its
  generalisation; a definition where its name is used (a use, `:type`,
  `:ls`), since a stored scheme is its Core's alone and stays general, so
  that a signature can keep a value polymorphic (`off :: forall (a : 3).
  Vec a m`; `forall a.` is a whole axis set, a length of its own included,
  and does not hold of a three-vector). `:type e` is the type of `it`, a
  named value, so `:type off` prints `Vec 3 m` while `:ls off` prints its
  signature. `e1`, `e2` and `e3` are anonymous where they are used. An
  anonymous value meeting a named one is the unifier's axes error with a
  hint, "give it a frame with `withAxes c v`, or `v to c` if it is along
  its space's base axes". `withAxes c v`, a primitive, reads an anonymous
  vector as along `c`'s axes, with no arithmetic. `noise` stays anonymous.
- **Written types.** A name in a length position resolves through the type
  scope to a minted axis type or a frame and means that many positions
  along it: `Vec lvlh m`, `Mat GCRS lvlh`, `Cov2 lvlh m (m/s)`. The number
  is the frame's own, read off its stored type (`card lvlh = 3`), not a
  fresh length: a fresh length in a signature is a quantified variable, so
  `v :: Vec lvlh m` would not hold of a definition of three positions and
  `:type`'s `Vec lvlh m` would not read back as itself. Since a signature,
  a data declaration or an ascription is read before the definitions of
  its group, a group's charts and what they depend on are entered first
  for their labels alone, then the whole group, so a chart and a signature
  naming its axes read in one group (an `:export`, the REPL's pending
  definitions).
- **Printing.** A named slot prints its name in place of the length (`Vec
  lvlh m`), by hash and then through the driver's naming as declared types
  are; an anonymous one its length; an axis variable beside a length
  variable is that variable (one binder); one beside a literal a sized
  binder, `forall (a : 3) d. Vec a d -> …`; any other, a second axis set
  beside a length that has one, a binder of its own (`det : forall n a.
  Mat n a -> Num`). Errors, `:lint` and `:core` print a named slot by name
  and an axis variable as its length.
- **Known gaps.** The store's log keeps a re-stamped definition's new
  version, not the step between, so a chart moved by `:rename` reloads
  without the intermediate binding in its history (as a `±` owner stamp's
  re-hash does); a chart redefined as no chart drops its axes' type label
  in the session but the log, which unnames a path for every kind, does
  not record it. A root chart's origin is along its space's base axes, so
  a named value there (`let o = [100, 200, 0] m`, `chart site on GCRS at
  o`) is refused as anonymous: the value needs `o :: forall (a : 3). Vec a
  m`. `withAxes`'s printed type does not show that its argument is
  anonymous, and `det`'s `Mat n a` reads back with a length of its own (no
  type yet says `card a ~ card n`). The first pass of a group that holds
  charts falls back to one pass when a chart needs the group's own data
  constructors, and then a signature or data field there naming the
  chart's axes is refused.

### 3.10 Units, spaces and frames

Decided by the owner, 2026-10-31. This is stage 3 of §3.9, revised: a point
is typed by its *frame* (`Point lvlh`, `Point degC`), not by its axes as
§3.9's decision 4 had it, and units become a type of their own. It is built
as one stage (the owner's choice) in two parts that land in order, units
(part U) and then frames (part F), since part F's `to` and quantity rule use
part U's machinery.

**The principle.** A chart is a step, an origin and axes. Each costs
something different to convert, and the type records exactly the parts whose
conversion is more than an exact multiplication:

| part | converting it | in an amount's type | in a point's type |
|---|---|---|---|
| step (scale) | multiply by an exact factor | no | no |
| origin | add an offset, possibly approximate or moving | no: it cancels | yes |
| axes | rotate, possibly approximate or moving | yes | yes |

Units are scale only, so a unit never enters a type: `1 km + 1 m` and
`5 deltaC + 9 deltaF` add with no `to`, and `to` chooses the unit a result
prints in (`5 deltaC + 9 deltaF to deltaC` is `10 deltaC`). Between frames,
conversion is explicit, as Haskell makes conversion between types explicit:
`20 degC .- 68 degF` is refused until one side is converted with `to`. Points
never add (`20 degC + 5 degC` is refused), whatever their frames.

#### Part U: units are syntax

Units are not first-class values. An ordinary expression carries an amount
(`Num d`, `Vec n d`, or `Tensor sh d`), a point, a chart, or another value.
To pass a scale to a function, pass `1 km`, not `km`. `Unit` and
`Quantity r` are not surface value types. Charts remain first-class.

**Unit contexts.** Unit expressions consist of declared unit names, products,
quotients and integer powers, with parentheses. They are used in quantity
suffixes (`5 km/h`), display conversion targets (`v to km/h`), chart steps
(`step km`), and `:prefer km/h`. A unit declaration accepts either such an
expression (`unit speed = km/h`, `unit metre = m`) or a computed scalar amount
(`unit deg = pi / 180 * rad`). It stores the unit internally, with its name,
scale and display hint. Dimensions in types continue to use unit names.

**Implicit one.** At an operand of ordinary `*` or `/`, a complete unit
expression is shorthand for one of that unit:

```
5 * km         = 5 * (1 km)
km / s         = (1 km) / (1 s)
x / km^2       = x / (1 (km^2))
x / (km/s)     = x / (1 (km/s))
```

The insertion is syntactic and respects local shadowing and namespace
resolution. It does not apply to arbitrary subexpressions, function arguments,
addition, comparisons, lists, or tuples. `km`, `km^2`, `km + m`, and `f km`
are refused outside unit contexts; write `1 km`, `1 (km^2)`, `1 km + 1 m`,
and `f (1 km)`. Sections expand normally: `(* km)` multiplies an amount by
`1 km`. Named primitives such as `outer` take explicit amount arguments.

**Grouping precedes insertion.** Preserve the quantity rule of §2.6: a
quantity consumes the following chain of declared unit factors, stopping at
an ordinary value or parentheses. Thus:

```
4 km / 2 km   = (4 km) / (2 km)    -- 2
4 km / km     = 4 (km/km)          -- 4
(4 km) / km   = (4 km) / (1 km)    -- 4
1 / 2 m/s     = 1 / (2 (m/s))      -- 0.5 s/m
1 / 2 * m / s = ((1/2) * (1 m)) / (1 s)
```

`unit u = s` creates a unit alias and participates in this grouping;
`let u = 1 s` creates an ordinary amount and ends a quantity suffix.
`let u = s` is refused. `let u = km/h` creates an amount, not a unit.

**Arithmetic and inference.** Public multiplication, division and powers
operate only on amounts. Multiplication keeps the shape concatenation rule;
division takes a scalar denominator. At generalisation an unresolved product
still defaults its left operand to scalar, yielding
`forall d s d1. Num d -> Tensor s d1 -> Tensor s (d*d1)` for `\a b -> a*b`.
There is no unit-role relationship to carry in a scheme. Applying a chart
still constructs a point, and points do not enter ordinary arithmetic.
A dynamic expression after a coordinate literal must be a chart; a dynamic
`to` target is a chart, with point versus vector conversion determined by types.

**Implementation and storage.** The evaluator retains internal `Unit`
objects for scale factors and display hints. Unit syntax lowers to those
objects; ordinary unit operands lower through `scale 1`. Compound unit
construction uses amount arithmetic and the internal `unit` wrapper. The
source printer reverses this construction in unit contexts, so declarations,
exports, and edits read back with the same hashes. `:prefer` uses the same
unit-only elaboration path as other unit contexts.

#### Part F: spaces and frames

**F1. Kinds.** Two new kinds: `Space`, and `Frame s` for a space `s`.
`ITS90 : Space`, `degC : Frame ITS90`. In a binder a space names
the kind of its frames, so `forall (c : ITS90).` means `c : Frame
ITS90`. A bare `forall c.` used as a frame gets the kind `Frame s` with
`s` generalised too: a frame on any space (kind polymorphism, the way a `d`
is inferred to be a dimension).

**F2. Spaces are declared.** A space is a set of points that convert among
each other: the temperatures, the instants of time, a physical space.

```
space ITS90 = Num K
space TT    = Num s
space GCRS  = Vec 3 m
```

A declaration mints a nominal space, as a chart mints its axes: two spaces
declared alike are two spaces, and points of one never convert to the other
(`20 degC to eci` is a kind error). It fixes the dimension and shape of the
space's amounts and gives the space a base: origin zero, the base unit as
step and, for a vector space, axes of its own, minted with it and named after
it (`Vec GCRS m`). The base is the reference every chart on the space is
given against in the end; no point is written on the base itself. A chart
names its space as its parent, `chart degC on ITS90 at 273.15 K`,
`chart JD on TT step day`; a chart with no `on` is refused, "name its
space: `chart … on ITS90`" (syntax in F10). This replaces §3.8's implicit base of a
dimension and, by the owner's decision, §3.9 decision 7's root chart that names its
own axes: a root
chart is a translated child of its space's base and has the base's axes, so
two translated roots on one space (`eci`, a lab bench) have one set of axes
and convert with `to`, and two on different spaces never meet.

**Naming spaces** (decided by the owner). A space is named after the
reference system that pins it down, as astronomy names ICRS, GCRS and ITRS,
never after the bare quantity: `Time` or `Temperature` reads as the one global
time, when a space is one of possibly many. The library declares:

- `TT` in `time` (Terrestrial Time), with `JD`, `MJD` and `J2000` (J2000.0 is
  JD 2451545.0 TT).
- `UTC` in `time`, with `unix`, which counts UTC seconds without leap
  seconds. There is no chart between `TT` and `UTC`: they differ by a
  constant plus the leap seconds, so the map is not affine and is an ordinary
  function over a leap-second table, not a `to`. A `unix` instant and a `J2000`
  one are different spaces, so mixing them is a kind error, not a silent error
  of about 69 s.
- `ITS90` in `temperature` (the International Temperature Scale of 1990),
  with `kelvin`, `degC`, `degF` and `degR`.

The library declares no pressure space: absolute pressure is an amount with a
natural zero, and a gauge chart's 101325 Pa is a convention, so a user who
wants one declares it. User spaces follow the same rule, `space GCRS = Vec 3
m`, `chart eci on GCRS`.

**F3. Frames.** A frame is the type-level identity of a chart: which origin
and which axes, with no numbers. Every chart has one. Whether a declaration
makes a new frame is decided by what it says, never by comparing values: an
origin may be approximate, and equality of computed values cannot be
decided.

- A chart directly on a space mints a frame: it is a root, and no point is
  written on a space's base itself.
- A chart with `at` (a new origin) mints a frame.
- A chart with `by` or `spinning` (new axes) mints a frame and its axes, as
  in §3.9.
- A chart on a chart with only a `step` (`chart mdegC on degC step mK`,
  `chart degR on kelvin step deltaF`) is a rescaling: it shares its parent's
  frame, its points have the parent's type, and its step is only how they
  print. Rankine written this way shares kelvin's frame, so Rankine and
  kelvin points subtract without a `to`.

A frame is named after the chart that mints it, so `chart degC on …` makes
`degC` a value (`degC : Chart degC`) and a frame (`degC : Frame
ITS90`), in separate namespaces as a chart and its axes are. Two
charts declared alike are two frames, like two `newtype`s over one type. A
chart with parameters mints one frame for all its arguments: `ecef (100
J2000)` and `ecef (200 J2000)` are two chart values of type `Chart ecef`. The relation
between the levels:

```
20 degC          : Point degC          -- a point on the frame
degC  (value)    : Chart degC          -- the chart: its step and origin
degC  (frame)    : Frame ITS90         -- the type-level name and its kind
ITS90            : Space
```

**What a declaration means** (decided by the owner). A chart declaration is
one frame, like one rigid body. Its parameters are that frame's
configuration, its degrees of freedom (a time, a joint angle, a state), and
never a choice between frames. It denotes the frame with a pose for each
argument, `pose(p) = (origin(p), rotation(p), step(p))` relative to the
parent. A point on it is coordinates in the frame, which do not depend on the
pose, as a seat's place on a train does not depend on where the train is. Two
bodies are two declarations; what they share is an ordinary function, not a
chart:

```
let lvlhTurn s = …                                   -- the recipe: a rotation for a state
chart lvlhA t on eci at (posA t) by lvlhTurn (stateA t)
chart lvlhB t on eci at (posB t) by lvlhTurn (stateB t)
```

`lvlhA` and `lvlhB` are sibling frames under `eci`, with axes of their own,
so their points and amounts never mix unconverted. One declaration used for
both, `lvlh (stateA t)` and `lvlh (stateB t)`, would make them one frame, and
`b .- a` would compare offsets from two spacecraft as if they were one body:
a misuse the checker cannot see, since it would have to compare argument
values. Charts are therefore declared when the code is written (decided by
the owner for now: metron is a small language of expressions over tensors); a
frame per item of data is an open question (§11).

**F4. Types.** `Point c` is the type of points on the frame `c`, and
`Chart c` the type of charts whose frame is `c`: one value for a fixed chart,
one per argument for a moving one. Two type functions read a frame:

- `Axes c`, its axis set: a rotated frame's own, a translated or rescaled
  frame's parent's, a root's its space's. In a written type a frame's name in
  an axis position means `Axes c`, and a space's name the base axes.
- `Diff c`, the type of amounts between points on `c`: the space's
  dimension along `Axes c`. `Diff degC = Diff degF = Num K`, `Diff lvlh =
  Vec lvlh m`, `Diff bench = Vec GCRS m` for a translated chart.

`Diff` is a synonym, not a new type (an associated type, not associated
data): amounts from frames with the same axes mix freely, because the scale is
applied into the value and the origin cancels. It reduces when the frame is
known, and to the space's dimension and shape once the space is known; on a
frame of an unknown space it stays residual, which a point operation accepts
as it is, and arithmetic on it is a pending constraint `Diff c ~ Tensor σ δ`.
`Point` keeps the frame, so `Point degC` and `Point degF` never unify.

**F5. Primitives.**

```
pointOn    : forall c. Chart c -> Coords c -> Point c        -- 3 degC, [1, 2, 3] lvlh; Coords c dimensionless, along Axes c
(.-)       : forall c. Point c -> Point c -> Diff c
(.+)       : forall c. Point c -> Diff c -> Point c
pointAt    : forall c. Chart c -> Diff c -> Point c          -- the amount from the origin along Axes c: [0, 0, 0] c .+ v, at any shape (7.7)
to         : forall s (c : s) (c1 : s). Point c -> Chart c1 -> Point c1
p.k        : Point c -> Num δ                                -- the k-th coordinate, the step applied
rotationOf : forall s (c : s). Chart c -> Mat s c            -- rows along the space's base axes, columns along c's
```

`withAxes`, `spinOf`, `originVelocityOf`, `velocityIn`,
`stateFrom` and `astro.State` are retyped over frames and spaces in the same
way. The checker needs no special rule for "convert first": `.-` takes two
`Point c`, so points on two frames fail to unify, reported as "points on degC
and degF: convert one with `to`"; a different origin is two frame names that
do not unify, different axes an `Axes` mismatch inside `Diff`, and a
different scale alone cannot fail.

**F6. Storage: chart coordinates** (§3.9 decision 4, kept). A point holds
its coordinates on its frame with the step applied, an amount from the frame's
origin along the frame's axes in base units, and its chart for printing. `20
degC` holds `20 K` above degC's origin; `p.0` reads a coordinate; printing
divides by the step, so a point prints on the chart it was written on with no
other arithmetic. Applying the step is an exact multiplication, while the
origin and the rotation, where error and motion come from, are applied only by
`to`, so arithmetic inside a frame never passes through them. `.-` and `.+`
within a frame are coordinate arithmetic; `to` maps through the tree, up to
the common ancestor and down. A point written on a rescaled chart and one on
its parent are on one frame and subtract directly.

**F7. Charts with parameters.** A chart's parameters are arbitrary, any
number of any type. An applied chart fixes its whole path to its space,
because a child's declaration either applies its parent to expressions of its
own parameters (linked: `chart lvlh s on (ecef s.epoch) at s.pos by …`) or
leaves the parent's parameters open, and they become parameters of the child
(inherited: `chart arm q t on (ecef t) at [1, 0, 0] m by roty q`). So a
conversion needs exactly two chart values, the source's and the target's.

A point on a parameterised frame holds its coordinates, and the chart it was
written on for printing only. Writing one needs an applied chart, `[1, 2, 3]
(ecef t0)`, because the step may depend on the arguments. Converting names
the source chart whenever it takes parameters, and a parameterised target is
given applied:

```
p from (lvlh s) to eci     -- p : Point lvlh
q to (ecef t)              -- the target applied
r to eci                   -- r on a chart without parameters: no from
p to eci                   -- refused: "lvlh takes arguments: write p from (lvlh …) to eci"
```

`p from c to c1` is typed `Point f -> Chart f -> Chart f1 -> Point f1`: the
chart after `from` must have the point's frame. The chart a point was written
on is never used for a conversion, so a wrong configuration is a missing
argument, not a silent error.

`.-` on one frame is frame-relative, whatever configurations its points were
written with. The other questions one asks of two points are conversions
followed by a subtraction:

1. On one frame: `b .- a`, relative to the frame (two cities on `ecef`).
2. Across the tree: `(sat to (ecef t)) .- station`, a satellite seen from a
   ground station, in Earth-fixed axes.
3. Both in a third frame. At one configuration this re-expresses the
   difference, `(b to (lvlhA t)) .- (a to (lvlhA t))`, which equals `(b .-
   a) to (lvlhA t)`. At two configurations it is a new quantity that
   includes the frame's motion between them, `(b from (ecef t1) to eci) .-
   (a from (ecef t0) to eci)`.

`b .- a on (lvlhA t)` is shorthand for the first form (F10); it covers only
points sharing a configuration.

**F8. The quantity rule for charts** (U4). Any expression of type `Chart c`
after a literal builds a point, so chart parameters, applied charts (`[1, 2,
3] (ecef t0)`) and local chart values need no declaration:
`pt :: forall (c : ITS90). Chart c -> Point c` with `pt c = 3 c` (a bare
number is a coordinate only on a scalar space, so `forall c` over every space
is too general, as built). Without a signature, the parameter is inferred
to be a chart over a scalar space. A
chart with parameters, unapplied, is a function and is refused after a
literal. The `chart` keyword is still what mints a frame.

**F9. Printing and encoding.** `:type 20 degC` is `Point degC`, `:type degC`
is `Chart degC`, `:type [1, 2, 3] lvlh` is `Point lvlh`; a point prints as it
did, `20 degC`, `[1, 2, 3] lvlh`. Spaces and frames are minted nominal types
like a chart's axes, with label kinds of their own that no source `data`
produces; a type that mentions them encodes them as appended tags (§6.1), and
the store format moves if the encoding does.

**F10. Syntax** (decided by the owner). A chart declaration is its name,
its parameters and its clauses, with no `=`:

```
chart name params… on parent [at origin] [step unit] [by B [then B …]] [spinning ω]
```

`on` is required and comes first: it ends the parameters and names the
parent, a space or a chart (applied, if it has parameters). The other clauses
come in any order, each running to the next clause word, so no expression in
them needs parentheses. `step`, `by`, `then` and `spinning` are words only
inside a chart declaration and stay free as names elsewhere; `at` and `on`
are keywords, and `on` also subtracts in a frame (below). An omitted clause is inherited: the origin and the axes are
the parent's, and the step is the parent's or, on a space, the space's base
unit. Which clauses appear decides whether a frame is minted (F3). `unit` and
`space` keep their `=`, since each binds one expression. The library's
charts, and §3.8's examples, read:

```
chart kelvin    on ITS90
chart degC      on ITS90 at 273.15 K
chart degF      on ITS90 at 459.67 deltaF step deltaF
chart degR      on kelvin step deltaF                    -- a rescaling of kelvin
chart JD        on TT step day
chart MJD       on TT at 2400000.5 day step day
chart J2000     on TT at 2451545 day step day
chart unix      on UTC
chart eci       on GCRS
chart ecef t    on eci by rotz (gmst t) spinning [0, 0, 1] * ω_e
chart lvlh s    on (ecef s.epoch) at s.pos by lvlhTurn s
```

**`to` is the one conversion.** It re-expresses its left side in the target
on its right, the reading chosen by types (U6): an amount in a unit
(display); a point on a chart (F7); an amount along a chart's axes, where only
the rotation applies, `(b .- a) to (lvlhA t)`. An amount on a frame with
parameters takes `from` as a point does, `v from (ecef t) to eci`.
`withAxes c v` labels a vector that has no frame, which is not a
conversion.

**Subtracting in a frame: `on`** (decided by the owner). `b .- a on c` is
`(b to c) .- (a to c)`: both points converted to one frame at one
configuration, then subtracted, `b .- a on (lvlhA t) : Vec lvlhA m`. `on`
binds like `to`, its left side must be a `.-`, and it is a keyword, the same
word as a chart declaration's parent clause, meaning "relative to" in both.
`in` could not serve: `let d = b .- a in (lvlhA t)` already parses as a `let
… in`. A point on a frame with parameters still needs its configuration, so
`on` covers only points whose conversion needs no `from`; otherwise the
desugared `to` is refused as F7 says, and the subtraction is written out.
**Deferred.** A frame per item of data (F3, §11); constraints over
`Diff` beyond the pending one (F4); printing values with `·` (§4.1).

**Part F, as built.** As decided, with these details the decision left
open, and two places where the library or an example could not be written
as decided, marked *deviation*.

- **Frames and spaces as types.** A frame in a type is its identity, a
  minted frame's hash or a frame variable (kind `Frame`), beside two
  companions, its axes (`Axes c`) and its space; a space is its identity, a
  declared space's hash or a space variable (kind `Space`), beside its
  shape (lengths only), its dimension and its base axes. A named frame or
  space carries its companions as its declaration fixed them, and a
  variable's companions are variables, so every relation F4 and F5 state
  is unification and none needs a lookup: `Point c` and `Point c1` meet by
  their identities, then their spaces and axes. This is the slot the brief
  asked for, as the axis slot is, not general kind polymorphism. `:type`
  prints a frame by its name and absorbs its companions: a frame's axes
  print as the frame (`Vec c m`), a space's base axes as the space (`Mat s
  c`), and a space variable is a binder only when two frames share it or
  its base axes are written, `forall s (c : s) (c1 : s)`; otherwise `forall
  c`. A binder names a frame's space, `(c : ITS90)` or `(c : s)`.
- **`Diff` and `Coords`.** One residual form, `Diff c` and the dimensionless
  `Coords c` (what `pointOn` takes, F5), reduced in substitution as soon as
  the space's shape is known, to the shape along `Axes c` in the space's
  dimension (or none). Residual `Diff` against a tensor of known shape fixes
  the space's shape; against one of unknown shape it is the pending
  constraint F4 names, solved when either is known, and one still pending
  when its definition is generalised is refused, "the amount between points
  on a frame of a space not known here: give a signature naming the space,
  as in forall (c : GCRS)", since a scheme cannot carry it.
- **Constraints on a space variable.** A binder can state its amounts:
  `forall (s : Space (Vec 3 m)) (c : s). Point c -> Point c` is the type
  of `let shift q = q .+ [1, 0, 0] m`. The space remains nominal and
  polymorphic; its shape and dimension are constrained. The amounts can
  be `Num d`, `Vec n d`, or `Tensor sh d` with a shape variable, and
  their variables are bound by the same `forall`. Printing includes these
  constraints when the body alone would not reconstruct them.
  A length binder `(n : Len)` gives `Vec n` anonymous axes. This lets
  `withAxes` retain the shared length between its space and its input
  without giving the input a separate, polymorphic axis identity.
  *Deviation:* F8's own example, `pt :: forall c. Chart c -> Point c` with
  `pt c = 3 c`, is refused as not as general as its signature: a number is
  the coordinate of a point on a space of numbers only, and `forall c`
  ranges over every space. Written `pt :: forall (c : ITS90). Chart c
  -> Point c` it holds, and the tests have both.
- **Declarations.** `space Name = type` takes `Num δ` or `Vec n δ` and mints
  a type labelled with its path (a label kind of its own, `SpaceLabel`),
  with two constructors: the tag a chart's Core names it by, and one that
  holds its amounts' type, so that a space's hash fixes what it is. A vector
  space mints its base axes with it, `Axes path`, as a chart's are. A frame
  is a type labelled `FrameLabel path moving`, minted when the clauses F3
  lists are written, and named as the chart in the type namespace; a
  rescaling mints none, and its name is refused where a frame goes,
  "`degR` is a rescaling and shares the frame of its parent: write Point
  kelvin". `space`, `on` and `from` are keywords; `step`, `by` and
  `spinning` are clause words in a chart statement only, and a chart's
  tokens are cut at them outside brackets, `then` separating generators. A
  clause given twice is refused, and one with no `on` is "name its space:
  `chart … on ITS90`, or the chart it is on".
- **Core.** Two primitives, no new Core constructor: `mkRoot frame {axes}
  space {step} {origin} {generators…} {spin}` on a space and `mkChart
  {frame} {axes} parent {step} {origin} {generators…} {spin}` on a chart,
  each clause a list of none or one (the generators any number), so that
  which clauses are written is in the term and an omitted one is
  inherited. Their schemes are computed from those lists and the tags, as
  `contract`'s are from its positions, `mkRoot`'s from the space's
  declaration. `:view` prints the clauses in the order `at`, `step`, `by`,
  `spinning`, and every chart reads back to its hash. The run time looks a
  space's declaration up by hash for the shape and dimension of an
  omitted origin and step.
- **Storage (F6).** A point holds its coordinates on its frame times the
  step, and the chart value holds its frame's hash and whether that frame
  takes parameters. `to` between charts of one frame relabels; between
  frames it follows local transforms up to the common configuration and
  down. Shared origins and rotations cancel before uncertainty arithmetic.
  Configurations match by frame identity and structurally identical local
  offsets and generators along their common path, never by approximate
  equality. Without a shared configuration the path reaches the space's
  base, giving `R_T⁻¹ (o_F + R_F x − o_T)`.
  `p.k` is an amount in the chart's step unit, on a space of one axis set.
- **Conversions.** `to`'s third reading, an amount along a chart's axes
  (`toAxes`), takes an amount along the space's base axes, on its leading
  position; `v from c0 to c1` (`axesFromTo`) takes one along `c0`'s axes,
  and `p from c0 to c1` (`fromTo`) a point. An amount carries no chart, so
  one along a turned frame's axes is converted with `from` even when that
  frame takes no parameters. The reading is chosen by the value's type
  once the target is a chart; a value still unknown is ambiguous at
  generalisation, and an amount before a target still unknown takes the
  unit reading, as before. A `to` from a frame whose chart takes
  parameters is refused when its frame is known, "lvlh takes arguments:
  write p from (lvlh …) to eci" (the operands as written), and at run time
  when only a frame variable is (`toE :: forall (c : GCRS). Point c ->
  Point eci`), never read off the chart a point was written on.
- **`on`.** `b .- a on c` desugars to `let x = c in (b to x) .- (a to x)`,
  one chart value for both, and prints so; it reads back to its hash.
- **`astro`.** `data State t r = State {epoch :: Point t, pos :: Vec r m,
  vel :: Vec r (m/s)}`: the epoch a point on a time frame, the position an
  amount from the space's base origin and both along its base axes, as
  F5's "rows along the space's base axes". *Deviation:* `velocityIn` and
  `stateFrom` need the chart's origin from the base, so `originOf : Chart c
  -> Vec s δ` is a new primitive beside `originVelocityOf`. Their inferred
  types constrain the space with `(s : Space (Vec 3 m))`. F10's `chart lvlh s on
  (ecef s.epoch) at s.pos by lvlhTurn s` works for a state whose position is
  along `ecef`'s axes (the tests use one); with `astro.State` the origin is
  `(s.pos - originOf (ecef s.epoch)) to (ecef s.epoch)`. Whether `State`
  should hold a point on a frame instead is the owner's to decide.
- **Declared types.** A `data` parameter used where a frame goes is a frame
  parameter, with its companions as parameters after the written ones (the
  axes of each length first, then each frame's axes and space's slot,
  shape, dimension and base); its axes cannot be written in a declaration,
  "no type says how many it has".
- **Listing.** `:ls --types` lists a frame as `frame degC` and a space as its
  declaration, `space ITS90 = Num K`; plain `:ls` leaves frames out,
  as their charts list. Minted axes print as their frame's or space's name.
- **Identity by path.** A chart redefined at its path keeps its frame, as
  its axes did (§3.9); a chart moved by `:rename` takes its frame and axes
  with it, re-stamped.
- **Known gaps.** A `data` declaration that names a chart's axes, pending in
  one group with a chart whose definition uses that declaration's fields,
  is read before the chart (§3.9's one-pass fallback): `:add` the chart
  first. The tests check every example of this part, the refusals, the
  sibling frames and the three subtractions.

## 4. Type system

Hindley-Milner with let-polymorphism, extended with dimensions after Kennedy
("Programming Languages and Dimensions", 1996; "Types for Units-of-Measure",
2009), type-level shapes for tensors, and two deferred constraints: shape
concatenation for the products and an equality instance (§4.2).

### 4.1 Types

```
τ ::= Tensor σ δ | Point φ | Chart φ | Diff φ | Coords φ | T a… | τ -> τ | α
a ::= τ | σ | δ | ν | χ | φ | ς      -- an argument of a declared type T, by the kind of its parameter
σ ::= [] | ν·χ : σ | s                 -- a shape: a list of positions, each a length and a name slot, possibly ending in a shape variable
χ ::= _ | A | x                         -- a name slot (§3.9): anonymous, a named axis set (a chart's or a space's minted type), or an axis variable
φ ::= F | c                             -- a frame (§3.10, F1): a chart's minted frame, or a frame variable, of kind Frame ς
ς ::= S | s                             -- a space: a declared space, or a space variable, of kind Space
δ ::= 1 | B | d | δ·δ | δ⁻¹          -- an abelian group, normalised
ν ::= k | n | n + k | rank s + k       -- a literal, a length variable, a variable plus a literal offset, or the rank of a shape variable plus one
```

`Num δ` abbreviates `Tensor [] δ`, `Vec ν δ` abbreviates `Tensor [ν] δ`, and
`Mat μ ν δ` abbreviates `Tensor [μ, ν] δ`. `Point c` is a point on the frame
`c` and `Chart c` a chart of it, for writing and printing its points (§3.6,
§3.8, §3.10 F4); `Diff c` is the amount
between two points on `c`, the space's amounts along `Axes c`, and `Coords
c` the coordinates a point is written with, dimensionless. A frame carries
its axes and its space, and a space its shape, dimension and base axes, as
companions: known for a named frame, variables beside a frame variable
(§3.10, part F, as built), so that `Diff c` reduces to a tensor once the
space's shape is known (`Diff degC = Num K`, `Diff lvlh = Vec lvlh m`) and
stays residual before. In a written type a frame's name where a length goes
means its axes, `Vec lvlh m`, and a space's name its base axes, `Vec
GCRS m`. `Point degC` prints for a point on `degC` and `forall c. Point c
-> Point c -> Diff c` for `\p q -> p .- q`; a binder names a frame's space,
`forall (c : ITS90)`, `forall s (c : s) (c1 : s)`.

`Unit δ` is internal to unit elaboration and display. It is not a writable
value type, and there is no surface `Quantity r` or role polymorphism.
Ordinary arithmetic takes amounts. Open tensor shapes print and parse as
`Tensor (n : s) d`, including longer chains such as `(n : m : s)`.

**Dimension syntax** (decided by the owner). A dimension is an ordinary
type argument. Square brackets mean one thing in a type, a shape (`Tensor
[2, 3] m`), as they mean a list of numbers in a vector literal.

```
Num K                     -- one name: bare
Vec 3 m, Vec lvlh m
Num (m/s^2)               -- compound: in parentheses
Num (kg·m²/s²)            -- unicode spelling; kg*m^2/s^2 in ASCII
Num (m²/(s²·K))           -- a denominator of several factors is grouped
Num (1/s)                 -- only negative powers
forall d d1. Num d -> Num d1 -> Num (d·d1)
Tensor [2, 3] (m/s^2), Point degC, Chart lvlh, Vec lvlh m
Num                       -- dimensionless
```

- **Inside the parentheses** a dimension is written as a unit expression:
  names (base units, declared units, `forall`-bound dimension variables),
  products with `*` or `·`, `/`, powers with `^k`, `^-k` or superscripts,
  parentheses for grouping, `1` for the identity. `*`, `·` and `/` share
  one precedence and associate to the left, as in an expression, so
  `m/s*kg` is `m·kg/s`. A dimension is a bare name only when it is one
  name to the first power; anything else is parenthesised.
- **A name in a dimension position** is a dimension variable when a
  `forall` (or a `data` parameter) binds it, and otherwise a unit, which
  means its dimension: `Num km` is `Num m`, `Num N` is `Num (kg·m/s^2)`.
  Which arguments are dimensions is fixed by the type constructor: the
  last of `Num`, `Vec`, `Mat` and `Tensor`, and a declared type's
  parameters of kind dimension. Required `forall` (§3.9, decision 6) is
  what makes the bare spelling unambiguous. `Point` and `Chart` take a
  frame, `Point degC`, `Chart degC` (§3.10, F4).
- **`·` is a token of its own.** In an expression `·` and `⋅` are the
  contracting product, as `@` is, and the unicode echo counts `·` for `@`.
  In a dimension `·` and `*` (and `⊗`, which lexes as `*`) are the product,
  and `@` is refused: "`@` is the matrix product; a dimension's product is
  * or ·".
- **Refusals.** Juxtaposition, `Num (m s)`, reads as a type application
  and is refused with "a dimension's product is written with * or ·, not
  by juxtaposition: write m*s"; the resolver says it of an application,
  the parser of a power followed by a name (`(m^2 s)`). Anything else
  where a dimension goes, a bracket among them, is "a dimension is a unit,
  a variable, 1, or a product of them in parentheses"; `Point K` is
  "unknown frame `K`" and `Point (Num K)` "a point and a chart are typed by
  a frame"; a unit where a length goes, `Vec m`, is "a vector's length
  comes first, Vec 3 m". A power outside parentheses, `Num m^2`, does not
  parse.
- **Printing** follows the same rule, so what `:type` prints reads back
  as itself: positive powers first, in the customary order (`kg m s A K
  mol cd rad`, variables last: `Num (m^2*d/s^2)`), then `/` and the
  negative powers, grouped when there are several; `·` and superscripts
  with unicode on, `*` and `^` with it off. Printing never writes a
  negative power, though `^-k` and `⁻ᵏ` read. A dimension standing alone,
  in an error message, prints without the outer parentheses: "dimensions
  differ by m/s". A point or chart as a declared type's argument is
  parenthesised, `Q (Chart degC)`. Typed Core's type applications print
  the argument form, `sq @(m/s)`, `sq @1`.
- **Values print** `9.81 m s^-2`: a value's units are a display spelling
  of the value, not a type, and keep the juxtaposed form.
- **The highlighter** colours a unit where a dimension goes, an argument
  (`Num m`) or a factor of a product (`(m/s^2)`), and leaves a name in a
  type's place plain (`(g → m) → {g}`); a `data` declaration's parameters
  are variables there as `forall`'s are.
- **Queries** (`:ls : Num d -> Num d`) stay implicit: `d` is not a unit of
  the library, so an unknown lowercase name is a variable.
- **Errors name variables as `:type` does.** `:type`, `:ls` and the `sig`
  line skip a name the type prints as a base symbol (`forall s1 d. Tensor
  s1 d -> Tensor s1 (s*d)`), and so does error printing (unifier errors,
  "not as general as its signature", lint), each name once and no base
  symbol: `Mat n k -> Mat n k m`, never a length `m` beside metres.
- **Known gap.** `:type cholesky` and `:type linalg.updateCov2` do not
  read back as signatures of themselves: the gap is the axis sets' (`det`'s,
  §3.9 "Known gaps"), not the dimensions'.

In a written type a name in a length position may be a chart's axes, `Vec
lvlh m`: that chart's number of positions along its minted type
(§3.9). A named slot prints by name in place of its length; an axis
variable beside a literal length prints as a sized binder, `forall (a :
3) d. Vec a d -> Vec a d`, and one beside a length variable as that
variable.

A declared type `T` (§2.3) is a type constructor with parameters of fixed
kinds, known from its definition, and `T a…` applies it to one argument per
parameter. Two applications unify when they are of the same type (the same
definition hash, §6.1) and their arguments unify kind by kind. A declared type
is identified by the hash of its definition, not by its name; the type that
inference prints as `#a3f9k` the driver renames (§7.2).

`Bool`, `(τ, τ, …)` and `{τ}` are not forms of their own: they are `T a…` on
the hashes of the three declarations the compiler holds (§2.3), `Bool` with
no arguments, a tuple of `k` components the tuple type of arity `k` applied to
them, and `{τ}` the list type applied to `τ`. They are written and printed in
their own syntax, by hash, whatever names them; `Bool` in a written type is the
built-in one. Unification, equality, exhaustiveness and lint treat them as any
declared type, except that two tuples of different arities fail with "expected
a tuple of 2 components, got one of 3".

**Variables are kinded.** There is one namespace of variables, each with a kind:
`Type`, `Len`, `Shape`, `Dim`, `Axis`, the name slot of a shape position
(§3.9), `Frame` and `Space`, the identities of a frame and a space
(§3.10, F1), with their companions. Each kind is an index
domain with its own equational theory and its own unifier: syntactic for types,
the offset rule below for lengths, element-wise for shapes, Kennedy's algorithm
for dimensions, syntactic for name slots. A written length variable stands
for a whole axis set, a length variable and a companion axis variable
introduced together, and a written literal length for anonymous axes
(§3.9). No term ever appears in a type, which is what keeps this on the
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
equal. Exponents are unbounded integers, never machine integers that wrap:
`:type 1 m^18446744073709551616` is `Num (m^18446744073709551616)`.

A shape is unified element-wise: two closed shapes must have the same rank and
unify position by position, the lengths and then the name slots; a shape
variable binds to any shape (with an occurs check). A shape variable can only
stand at the tail, so `n : s` means "rank at least one". Shape polymorphism is what lets `+`, `-`, `neg` and `vmap` have one
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
(*) (⊗)  outer : Tensor s1 δ1 -> Tensor s2 δ2 -> Tensor (s1 ++ s2) (δ1·δ2)   -- tensor product; scalar scaling is the rank-zero case
(·) (@)  dot   : Tensor (s1 ++ [n]) δ1 -> Tensor (n : s2) δ2 -> Tensor (s1 ++ s2) (δ1·δ2)   -- contracting product: dot, Mat·Vec, Mat·Mat
(∧) (/\) wedge : Vec n δ1 -> Vec n δ2 -> Mat n n (δ1·δ2)                       -- antisymmetrised outer product; the general binary product of vectors
(⋆)      star  : Mat 3 3 δ -> Vec 3 δ                                          -- 3D Hodge dual
(×) (><) cross : Vec 3 δ1 -> Vec 3 δ2 -> Vec 3 (δ1·δ2)                         -- prelude: cross a b = star (wedge a b)
(⊙) (.*) emul  : Tensor s δ1 -> Tensor s δ2 -> Tensor s (δ1·δ2)               -- elementwise
(⊘) (./) ediv  : Tensor s δ1 -> Tensor s δ2 -> Tensor s (δ1/δ2)
(/) (÷)  div   : Tensor s δ1 -> Num δ2 -> Tensor s (δ1/δ2)                     -- division by a scalar
```

`dot`'s contracted positions, the left's last and the right's first, are one
length and one name slot (§3.9), so contracting along different axis sets is
a type error once named sets exist.

The types of `outer` and `dot` mention shape concatenation `s1 ++ s2`, which is
not a syntactic shape when the rank of `s1` is unknown. Inference therefore
records a **shape-append constraint** `s3 ~ s1 ++ s2` and solves it as soon as it
can:

- when `s1` is closed (ends in `[]`), `s3` is the cons chain of `s1`'s lengths in
  front of `s2`, which the shape language expresses directly;
- when `s2` is scalar, `s3` equals `s1`, including an unknown-rank tensor;
- when `s2` and `s3` are both closed, `s1` is the prefix of `s3` of rank
  `rank s3 - rank s2`, and the remainder unifies with `s2`;
- otherwise the constraint waits. Every step is first-order and unitary.

At a generalisation point a constraint whose variables are all about to be
quantified cannot wait any longer and is **defaulted**: the unknown part of
the left operand takes the least rank the constraint allows. A left operand
whose rank is not known at all is therefore a scalar for `outer` (so `\k v
-> 2 * k * v` gets `Num -> Tensor s -> Tensor s`) and a vector for `dot`.
An operand that already has leading lengths keeps them and gains only
those the result still needs: `\x -> [[x]] · [2]` makes `x` a scalar and
`[[x]]` a matrix, giving `Num -> Vec 1`; `\x -> [x] * [1]` gives `Num ->
Mat 1 1`; and in `\x -> (x · [[1, 2]]).0.1` the result's two lengths make
`x` a matrix. Defaulting the whole operand to a scalar or a vector would
refuse these, though each checks once `x`'s rank is known. The two
constraints of one `dot` share the left's leading part, so that part
takes the most lengths either of them needs. This is the one place the type system guesses, it
guesses the common case, and it is the rule that dictionary passing will
later remove: when data constructors exist, an unresolved constraint
becomes a parameter of the definition instead of a default, and `\k v ->
2 * k * v` becomes polymorphic in the rank of `k`.

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
`Tensor s` and `Point s d`, and structured data whose components have
equality: a declared type `T τ…` when every field of every constructor, at
those arguments, does. `Bool`, tuples and lists are declared types (§4.1),
so `Bool` has equality outright, a tuple when every component does and a list
when its element does, by the same rule and no rule of their own. Values of data types are equal when their constructors are
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

`*` and `/` take amounts. Units at their operands are elaborated as explicit
amounts before inference (§3.10). There is no public role polymorphism.

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
                        where lb is the variable la: the paired lengths are one length, and their axes one slot
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
matrices of any size until the length-as-exponent relation `Num (d^n)`
exists (§4.6). Display
units, the prelude and `to` with a display hint are the remaining pieces of
roadmap item 2. Units are syntax (§3.10, part U). The internal primitives
use Unit objects for suffixes and display targets; ordinary arithmetic takes
amounts. The Unit signatures below describe Core, not surface value types.

```
literal     : Num 1
m           : Unit m          kg : Unit kg     s : Unit s     (etc.: a base unit is a unit, 3.10)
(+) (-)     : Num d -> Num d -> Num d                    (and Vec, Mat instances)
(*)         : Num d1 -> Tensor s d2 -> Tensor s (d1*d2)   -- also the product table of 4.2
(/)         : Tensor s d1 -> Num d2 -> Tensor s (d1/d2)
(== /=)     : Num d -> Num d -> Bool                     (and Vec, Mat)
(< <= > >=) : Num d -> Num d -> Bool
(&& ||)     : Bool -> Bool -> Bool          not : Bool -> Bool
to          : Tensor s d -> Unit d -> Tensor s d         -- a display unit (3.2.12, 3.10 U6); toChart and toAxes for a chart, below
scale       : Tensor s 1 -> Unit d -> Tensor s d         -- the quantity rule after a unit, `3 km`, `[1, 0, 0] (km/h)` (2.6, 3.10 U4)
unit        : Num d -> Unit d                         -- internal unit construction
(±) (±σ)    : Num d -> Num d -> Num d                    (and Vec, Mat)
sqrt        : Num (d^2) -> Num d
abs         : Num d -> Num d
mid         : Tensor s d -> Tensor s d               -- per component: the midpoint, exact (3.2.9)
bound       : Tensor s d -> Tensor s d               -- per component: Σ_bound |cᵢ| + slack, exact
sd          : Tensor s d -> Tensor s d               -- per component: √(Σ_stat cᵢ²), exact or enclosed
floor ceil round : Num 1 -> Num 1
sin cos tan : Num rad -> Num 1
asin acos atan : Num 1 -> Num rad
sinh cosh tanh exp log : Num 1 -> Num 1
atan2       : Num d -> Num d -> Num rad
mkRoot      : Frame F -> {Axes A} -> Space S -> {Unit d} -> {Tensor σ d} -> {Mat n n} -> {Vec 3 (rad/s)} -> Chart F   -- a chart on a space: its frame, its axes if turned, the space, then its clauses, each a list of none or one; d, σ the space's (3.10 F3, F10)
mkChart     : {Frame F} -> {Axes A} -> Chart p -> {Unit d} -> {Diff p} -> {Mat n n} -> {Vec 3 (rad/s)} -> Chart F'   -- a chart on a chart: F' is F if minted, else p (a rescaling); its axes A if turned, else p's (3.10 F3)
rotationOf  : Chart c -> Mat s c                        -- the absolute rotation, rows along the space's base, columns along the frame's axes; computed once per chart; exactly I when not turned (3.8, 3.10)
spinOf      : Chart c -> Vec s (1/s)                    -- the absolute angular velocity, base axes; exactly 0 when nothing spins (3.8)
originVelocityOf : Chart c -> Vec s (d/s)               -- the velocity of the origin, base axes; exactly 0 when nothing above spins (3.8)
originOf    : Chart c -> Vec s d                        -- the origin from the space's base origin, base axes (3.10, part F as built)
withAxes    : Chart c -> Vec n d1 -> Vec c d1           -- anonymous axes read as the chart's; no arithmetic (3.9)
pointOn     : Chart c -> Coords c -> Point c            -- what the quantity rule builds for `20 degC`, `[1, 2, 3] site` (3.10 F5)
pointAdd    : Point c -> Diff c -> Point c              -- `.+`
pointAt     : Chart c -> Diff c -> Point c              -- an amount from the chart's origin along its axes (7.7)
pointSub    : Point c -> Point c -> Diff c              -- `.-`
toChart     : Point c -> Chart c1 -> Point c1           -- `p to c1`, c and c1 frames of one space (3.10 F5)
fromTo      : Point c -> Chart c -> Chart c1 -> Point c1   -- `p from c to c1` (3.10 F7)
toAxes      : Tensor (n·s : t) d -> Chart c -> Tensor (n·c : t) d     -- `v to c`, v along the space's base axes (3.10 F10)
axesFromTo  : Tensor (n·c : t) d -> Chart c -> Chart c1 -> Tensor (n·c1 : t) d   -- `v from c to c1` (3.10 F10)
p.i         : Point c -> Num δ                          -- a coordinate, the step applied; δ the space's dimension (3.10 F5)
covariance  : Vec n d -> Mat n n (d^2)                  -- Σ cᵢcᵢᵀ over the statistical nudges (3.5)
crossCovariance : Vec n d1 -> Vec m d2 -> Mat n m (d1*d2)   -- Σ cᵢc'ⱼᵀ over the statistical nudges both share; exact; display unit as for * (3.5, 3.7)
cholesky    : Mat n n (d^2) -> Mat n n d
vzipWith    : (Num d1 -> Num d2 -> Num d3) -> Tensor s d1 -> Tensor s d2 -> Tensor s d3   -- per component pair, no display unit (3.3)
indices     : Vec n d -> Vec n                          -- [0, 1, …, n-1], exact; the argument's components are not read
timap       : (Vec (rank s) -> Num d1 -> Num d2) -> Tensor s d1 -> Tensor s d2   -- the multi-index, exact, then the component; no display unit (3.3, 4.1)
x ± e, x ±σ e : Tensor s d -> Num d | Tensor s d -> Tensor s d   -- per component (3.4)
v ±σ P      : Vec n d -> Mat n n (d^2) -> Vec n d       -- a vector with covariance P (3.5)
pi e        : Num 1
e ^ n       : Num d -> Num (d^n)   -- special form, n an integer literal
noise n     : Vec n 1                        -- special form, n a natural literal
gauss n     : Vec n 1                        -- special form, n a natural literal
det         : Mat (n·a) (n·b) 1 -> Num 1    -- a plain primitive, any n; dimensionless only; rows and columns may be two axis sets (4.6, 3.9)
expm        : Mat n n 1 -> Mat n n 1        -- a plain primitive, any n; dimensionless in and out; one axis set (3.3)
transformBy : Mat (n·_) (n·_) 1 -> Tensor s d -> Tensor s d   -- R along every axis; every length of s must be n, checked at run time; anonymous axes (3.3, 3.9)
v.i         : Vec (n + i + 1) d -> Num d    -- special form, i a literal position
m.i         : Mat (k + i + 1) n d -> Vec n d
contract i j t : Tensor (l0 : … : lj : s) d -> Tensor (… without i and j : s) d   -- special form, i ≠ j literal naturals, li = lj (4.2)
permute [p…] t : Tensor (l0 : … : lk-1 : s) d -> Tensor (lp0 : … : lpk-1 : s) d -- special form, a literal permutation of 0 .. k-1 (4.2)
slice k i t : Tensor (l0 : … : lk-1 : n + i + 1 : s) d -> Tensor (l0 : … : lk-1 : s) d -- special form, k and i literal naturals; t._.i (2.10, 4.1)
```

Each length in these types is a position with a name slot (§3.9), written
`n·a` where it matters (not syntax) and otherwise as the length alone: a
length variable has an axis variable beside it and a literal `3` of the
three-dimensional primitives one too, shared where the axes are one set, and
`_` is anonymous. `Frame F`, `Axes A` and `Space S` are the types of the
constructors a chart or space declaration mints (§3.10, F3), and the
primitives read `F`, `A` and `S` off those arguments as `contract` reads
its positions; a frame's space, shape and dimension are its companions
(§4.1), so `s` and `d` in the rows above are the space's base axes and
dimension, solved once the frame is known. `Diff c` reduces to a tensor once
the space's shape is known. Which slots are shared is listed in §3.9 under
"As built", and the frame companions in
§3.10 under "Part F, as built".

The circular functions take an angle and their inverses return one (§3.2.11):
`rad` is a base unit and `deg = pi / 180 * 1 rad`, so `sin (90 deg)` type-checks,
`sin (1 m)` fails, and so does `sin 1`, with a message that asks for `1 rad` or
`45 deg`. `atan2 : Num d -> Num d -> Num rad` accepts any one dimension for
its two arguments. The hyperbolic functions, `exp` and `log` take plain numbers.

`transformBy` is the one primitive with a run-time shape check. Its
argument may have any rank, but every length must be the matrix's `n`, a
shape `[n, n, …, n]` of unknown rank, which the shape language cannot
write: a shape is a list of lengths with a variable tail (§4.1), with no
"every element is `n`". So the type is `Mat n n -> Tensor s d -> Tensor s
d` and the evaluator refuses another length, "transformBy: every axis must
have length n: the matrix is 3 × 3 and the tensor's lengths are [3, 2]".
A richer shape language would make this a type error (§11).

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

Worked example, `sqrt (x * x)` with `x : Num d₁`. `x * x : Num (d₁^2)`. `sqrt`
expects `Num (d^2)`. Unify `d^2` with `d₁^2`: `δ = d^2 · d₁^-2`. Smallest
exponent is 2 (tie, pick `d`). 2 divides -2, so `d := d₁`. Result:
`sqrt (x * x) : Num d₁`, as it should be.

Example needing the Euclid step: unify `d₁^2 · d₂^3` with `1`. Smallest is
`x₁ = 2` on `d₁`; 2 does not divide 3. Substitute `d₁ := d₁' · d₂^(-⌊3/2⌋) =
d₁' · d₂^-1`. Now `δ = d₁'^2 · d₂^-2 · d₂^3 = d₁'^2 · d₂`. Smallest is 1 on `d₂`,
which divides 2, so `d₂ := d₁'^-2`. Composed: `d₂ = d₁'^-2`, `d₁ = d₁'^3`. Check:
`d₁'^6 · d₁'^-6 = 1`. These are exactly the solutions of `2a + 3b = 0`.

Non-unifiable example: `Num m` with `Num s`. `δ = L · T^-1` has no variables
and is not empty, so `1 m + 1 s` is rejected with

```
type error: cannot add Num m to Num s: dimensions differ by m/s
```

### 4.5 Inference

Standard algorithm W over Core (§5.1), dispatching to §4.4 at `Num`, `Vec`,
`Mat`, and emitting §4.2 constraints at overloaded operators. A binding group is
split into strongly connected components (§6.3); each component is inferred
monomorphically, then generalised over its free type, dimension and length
variables. Printed schemes are headed by `forall` and their variables
(§4.8), use `a b c` for type variables, `d d1` for dimension variables, `n
m` for lengths and `s s1` for shapes, and show dimensions with base-unit
symbols:

```
> :type \r -> pi * r^2
forall d. Num d -> Num (d^2)
> :type (*)
Mul a b c => a -> b -> c
> :type 9.81 m/s^2
Num (m/s^2)
```

### 4.6 Known limitations

- A signature (§4.8) is checked after inference, not used during it, so
  there is no polymorphic recursion: inside a cycle a member's recursive
  uses see its one monomorphic type, whatever its signature says, and a
  definition that needs its own signature to check does not check. The one
  exception is a reading (§3.10): a quantity or a `to` whose reading the
  types choose is first inferred with the definition's signature as an
  ascription of its body, and the reading found is written into the term,
  which is then inferred alone as before (`pt c = 3 c` stores `pointOn c 3`). The definition's own
  ascriptions do not take part, since they are not in its term.
- `^` requires a literal exponent, because `x ^ y` with a runtime `y` has no static
  dimension. `sqrt` covers the `1/2` case; a `cbrt` can follow.
- `det` is on dimensionless matrices only. Its natural type, `Mat n n d -> Num
  (d^n)`, needs a length as a dimension exponent, which the type system does
  not have. So `det : Mat n n 1 -> Num 1` (`:type det` prints `forall n.
  Mat n n -> Num`): it is polymorphic in `n` with no static size check, so `let d a =
  det a` generalises and works at every size. A matrix with a unit is a type
  error ("expected Mat n n, got Mat 2 2 m"); divide the unit out first, as
  in `det (a / (1 m))`, and multiply by `m^n` for the size at hand.
- Dimension polymorphism is let-polymorphism.
- `rank` is the only type-level function, and a type cannot say that two
  unknown shapes have the same rank: a definition that needs that, such as
  `\f t u -> (timap f t, timap f u)`, is refused at generalisation (§4.2).
- Vectors and matrices are homogeneous in dimension (§3.3); a matrix of
  mixed dimensions is written as blocks (§3.7).
- Component access needs a literal position (§2.10). Computed indices do not exist.
  The same holds for the positions of `contract` and `permute` (§4.2): a
  function cannot take them as parameters, so `\i -> contract i 0 t` is an
  error.
- A pending relation between `Diff c` and an unknown tensor shape cannot
  be carried by a generalised scheme. Give a signature naming the space
  or constraining its amounts, as in `(s : Space (Vec 3 m)) (c : s)`.

### 4.7 Error reporting

**What is static.** A binding group is parsed, desugared, inferred and elaborated
as a whole, and nothing in it is stored or evaluated unless all of that succeeds.
The one-shot CLI checks a whole file first. Every error below is reported at that
point, before any arithmetic runs:

| Expression | Error | Found by |
|---|---|---|
| `1 m + 4.5 s` | dimensions differ by `m/s` | dimension unifier, §4.4 |
| `[1, 2] + [1, 2, 3]` | lengths 2 and 3 differ | length unification, §4.1 |
| `[1, 2].2` | position 2 out of range for length 2 | length unification, §4.1 |
| `1 + true` | `Num` versus `Bool` | HM unification |
| `sin (1 m)` | `sin` needs `Num 1`, got `Num m` | dimension unifier |
| `[[1, 0], [0, 1]] * [1, 2, 3]` | no instance `Mul (Mat 2 2) (Vec 3)` | overload solver, §4.2 |
| `if 1 then 2 else 3` | condition is `Num`, needs `Bool` | HM unification |
| `x ^ y` with non-literal `y` | exponent must be a literal | parser |
| `det a` with `a : Mat 2 2 m` | expected `Mat n n`, got `Mat 2 2 m` | dimension unifier |
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
still sees the syntax, printed under a type error that lands there. The
hints: a literal argument followed by a unit name (`Rect 3 m 4 m`) is two
arguments, and the error says to write `(3 m)` (§2.6); a unit's name where
an amount goes, or beside an amount under `*` or `/`, "`s` is a unit; write
`1 s`" (§3.10, U3); and a name that ends a quantity, "`u` is not a declared
unit, so the quantity ends before it; if it is a unit, write 9.81 (m/u)"
(U5).

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
    cannot add Num m to Num s: the dimensions differ by m/s
  ```

- Runtime errors reuse the table: a `PrimApp` that divides by zero or a comparison
  that cannot be decided reports its path, so the message points at the operation
  even though it failed during evaluation.
- Definitions already in the codebase have no source text. When an error involves
  a `Ref`, the message names the definition and its stored type
  (`period : Num m -> Num s`) instead of a span, and `:view` is how the user
  gets at its body.

The provenance table lives for one REPL interaction or one file. It is never
stored, so hashes and the codebase are unaffected, and the evaluator's type-error
cases are placeholders that elaboration makes unreachable.

### 4.8 Type annotations

A **signature** `name :: type` (§2.2) says what type a definition is to
have. The type is written as `:type` prints types (§2.3), in the scope of
the statement. **Its variables are bound by `forall`** (§3.9, decision 6):
`ident :: forall a. a -> a`, `norm2 :: forall n d. Vec
n d -> Num (d^2)`, `∀` for `forall`. Every other name in it is a name and
resolves like one: a built-in type, a declared type, a base unit or a
unit, by the scope. An unknown lowercase name is an error, not a guessed
variable:

```
f :: a -> a
error at 1:6
  f :: a -> a
       ^
  unknown name `a` in a type; bind it with forall if it is a variable
```

and an unknown capitalised name is an unknown type. A type
without variables needs no `forall`: `area :: Shape -> Num (m^2)`.

- **Kinds come from use**, as a `data` parameter's do (§2.3): `a` in `a ->
  a` is a type, `n` in `Vec n` a length, `s` in `Tensor s d` a shape, `d` a
  dimension. A variable used at two kinds is refused. A length variable
  stands for a whole axis set, its length and a companion axis variable
  (§3.9). A binder that is not used binds nothing.
- **A sized binder**, `forall (a : 3) d. Vec a d -> Vec a d`, is a length
  fixed to the literal beside axes of its own: "any three-axis set, the same
  one throughout". It accepts a `Vec 3` of any axes and refuses a `Vec 2`
  with the lengths message, and a definition that holds of it must be
  polymorphic in those axes (`let keep v = v` is). Used as anything but a
  length, it is refused.
- **A binder shadows** a unit, a base unit or a declared type of its name
  throughout its type, brackets included, and, for a signature given with
  its definition, in the types of that body's ascriptions (below); never
  in an expression. In `same :: forall s d. Tensor s d -> Tensor s d`, `s`
  is the shape variable; in `secs :: Num s -> Num s` it is the second;
  in `forall s. Num s -> Num s` it is a dimension variable, and the
  body of either definition still reads `1 s` as the second. A binder is a
  lowercase name other than `rank`, bound once, so only a lowercase
  declared type can be shadowed, and a binder used as a head, `a Num`, is
  refused as taking no arguments.
- `forall` goes only at the head of a signature's or an ascription's type;
  `data` parameters are already explicit, and a field cannot hold one.

**Printing.** `:type`, `:ls` (definitions and constructors), and every place
a signature is written back (`:edit`, `:export`, `:scratch`'s `pending:`
line and the `sig` log line, §7.4) print the `forall` when the type has
variables, in the order the printer names them, so what is printed can be
pasted back: `forall a. a -> a`, `forall n d. Vec n d -> Num d`. A type
without variables prints without one. Variables are named by kind
(`a b c`, `n m k`, `s s1`, `d d1`); since a binder shadows a unit of its
name, a name is skipped only when the same type prints that base symbol in
a dimension, so a shape variable beside the second is `s1`: `forall s1 d.
Tensor s1 d -> Tensor s1 (s*d)`. Axis variables print as nothing and are
not bound, except beside a sized binder, which prints sized: `keep ::
forall (a : 3) d. Vec a d -> Vec a d` (§3.9, decision 6). Error messages,
`:lint` and `:core` print types without `forall`. `forall` prints so in
unicode mode too; `∀` is input only.

**Queries stay implicit.** A `:ls : type` query is a search pattern, not a
type to read back, so its unknown lowercase names are variables (`:ls :
{a} -> Num` finds `length`). A query headed by `forall` reads as a
signature does, and so does a `sig` log line.

**Meaning: an instance of the inferred scheme.** A signature is checked
after the definition's component has been inferred and linted, never used
while inferring it. It holds when its type, with its own variables held
fixed as if they were constants, is an instance of the inferred scheme:
there is a substitution of the *inferred* scheme's variables that gives
the signature's type (`Metron.TCore.signatureHolds`, one-way matching of
each kind, the same matching lint uses for type applications). So a
signature can narrow a definition's type and never widen it:

```
f :: Num m -> Num m
let f x = x                     -- holds: a := Num m

f :: forall a. a -> a
let f x = 1                     -- refused, at the signature:
error at 1:1
  f :: forall a. a -> a
  ^^^^^^^^^^^^^^^^^^^^^
  `f`'s definition has type `a -> Num`, not as general as its signature `a -> a`
```

**Label-level.** A signature belongs to the name, not to the hash: it is
kept beside the names, as `unit` and `chart` flags are (§3.2.12, `Codebase.signatures`),
never changes a term's hash, and two names of one hash may carry different
signatures, one signed and one not. `:type f`, `:ls` and `:edit` show the
signature of a signed name; an unsigned name shows its definition's own type,
as before. A later input that redefines a signed name is checked against the
stored signature, and refused with the same message at the redefinition,
unless the same input gives a new signature. A propagation (§7.5) that would
move a signed name to a version its signature does not hold of leaves it on its
version, with the reason. `:rename` and `:move` take the signature with the
name; `:alias` does not copy it, because an alias is the hash, unsigned;
`:unname` removes it. A signature for a stored definition may also be given
alone, `f :: Num m -> Num m`, and `:add` reports `signed f`. A
signature names declared types by hash, so when `:rename` re-hashes a type
(§7.2) or `:edit` replaces one (§7.3), a signature that names it follows to
the new type, unless its definition was left on the old one.

**Uses see the signature.** A reference written under a signed name, while
the name still points at that hash, is typed by the signature: inference
instantiates the hash's own scheme, which is what the type applications in
Typed Core record and lint checks, then instantiates the signature and
unifies the two (always possible, since the signature is an instance).
With `f :: Num m -> Num m` and `let g x = x` (the same hash, unsigned),
`f (3 s)` is refused with "expected Num m, got Num s" while `g (3 s)` is
`3 s`.

A definition's stored types and Typed Core are always those of its Core
alone, because the store recomputes them from the terms on load (§7.4),
before the labels are replayed, and because two definitions that differ only
in the names they were written with are one hash. So a definition that uses
a signed name is checked twice: inferred and stored as before, then checked
again with the signatures its references see, which may refuse it. Its
own type stays its Core's: `let h y = f y` has type `a -> a`, and `h (3 s)`
is `3 s`. To narrow `h`, sign it: a signature is checked against the type
the second check inferred, `Num m -> Num m` here, so `h :: Num m ->
Num m` holds and `h :: forall a. a -> a` is refused. §11 has this as
open.

**Ascription.** `(e :: type)`, anywhere an expression goes, in parentheses
as a tuple or a section is, gives `e` a type. The type is converted in the
scope of the expression as a signature's is: its variables are bound by
its own `forall`, or by the signature of the definition it is in (below),
and an unknown lowercase name is the same error. Each of its own variables
is fresh, and the type is unified with `e`'s inferred type at `e`'s node,
so an ascription narrows and never widens: `(1 :: forall a. a)` is `1`, of
type `Num`, because `a` is a fresh variable that unifies with `Num`;
`:type \x -> (x :: forall d. Num d)` is `forall d. Num d -> Num d` where
`\x -> x` is `forall a. a -> a`; `(3 m :: Num m)` is `3 m`. Two
ascriptions whose own `forall`s both bind `d` do not share it. A failure is
reported at the ascription, in the usual form with the prefix "the
ascription":

```
> (3 m :: Num kg)
error at 1:1
  (3 m :: Num kg)
  ^^^^^^^^^^^^^^^^^
  the ascription: expected Num kg, got Num m: dimensions differ by kg/m
```

An ascription does not reach Core. The desugarer puts `e` in its place,
and the term it builds is the one that is hashed, stored and run; it only
notes the written type beside the provenance (`Provenance.ascriptions`).
When there is any, the input is desugared a second time for checking
alone (`Desugar.desugarMarked`), where each ascription is a marker, a
primitive application under a reserved name `§ascribe…` around `e`, that
the user cannot write. Inference reads the marker by its name, takes the
converted type from the annotations (`Infer.Annotations`, beside the
signatures), unifies, and elaborates the marker to `e`'s own typed term,
so no marker reaches Typed Core. A marker identifies the node itself,
which a path into the term would not: the provenance paths of the
desugarer and the paths inference walks part ways inside `case`
alternatives, `if` branches and list literals (§11). An error in the
ascription is recorded under a key of its own and so always points at
it. So `:view` and `:core` have nothing to show for an ascription: `let f
x = (x :: Num m) + 1 m` views as `f = \x -> x + 1 * m`. An expression's type is narrowed (`:type`, and what it
evaluates to), but inside a definition an ascription only checks: the
definition's type is its Core's, as for a use of a signed name above,
because the store recomputes types from the terms, which have no
ascriptions. `let g x = (x :: Num m)` is `forall a. a -> a`, the same
hash as `let g x = x`; sign `g` to narrow it.

**Scoped variables.** A signature's `forall` scopes its variables over the
body of its definition, when the signature is given in the same input as
the definition (a stored signature keeps no names, so a redefinition
alone does not see them): an ascription in the body may name them, and
they are the signature's variables, not fresh ones. An ascription's own
`forall` shadows one of the same name.

```
f :: forall a. a -> a
let f x = (x :: a)                    -- holds: x has the signature's a

g :: forall a b. a -> b -> a
let g x y = (x :: b)                  -- refused, at the signature:
  `g`'s definition has type `a -> a -> a`, not as general as its signature `a -> b -> a`
```

Without the scope, `(x :: b)` would only narrow `x`, which any type does,
and `g` would hold. With it, the check that ascriptions take part in
(above) wraps the definition's body in a marker for the signature itself
(`Desugar.signatureMarker`), which unifies the body's type with the
signature's, and the ascriptions' converted types refer to the same
variables, renumbered into a range of the member's own that no variable
of inference meets (`Resolve.scopedSignature`). These unify as any
variable does; the signature is then checked, as always, against the
scheme that check gives, so an ascription that narrowed one of its
variables or made two of them one is refused with the usual "not as
general" message at the signature. This happens only when an ascription
names one of the signature's variables, so a definition without one
checks exactly as before; it applies to each member of a cycle with its
own signature. A failure to unify the body with the signature in that
check is reported with the prefix "the signature".

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
con    ::= UserCon hash i                  -- constructor i of the declared type with that definition hash
Kind ::= Bound | Stat
```

There are no built-in constructors: `true`, tuples and lists are constructors
of the three declarations the compiler holds (§2.3), referenced by hash like
any other. With `False`, `True`, `Pair`, `Nil` and `Cons` standing for those
references, `if c then a else b` is `Case c [Alt False [] b, Alt True [] a]`;
`true` is `Con True []`; `(a, b)` is `Con Pair [a, b]` and `(a, b, c)` the
constructor of the three-component tuple type; `{a, b}` is `Con Cons [a, Con
Cons [b, Con Nil []]]`. Alternatives follow the constructors' declaration order
(`False, True`; `Nil, Cons`; a declared type's as written) and cover every
constructor of the scrutinee's type; a surface `_` is expanded into the
missing alternatives, so Core has no default case. A constructor is
referenced by its type's definition hash and its position, never by name, so
renaming a constructor changes no term (§7.2) and a term's hash depends on
the type's definition, not on what it is called.

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
  `PrimApp "scale" [Lit 3, PrimApp "m" []]`, `3 km` the same over `Ref #km`,
  and `20 degC` `PrimApp "pointOn" [Ref #degC, Lit 20]`; where the spelling
  does not decide, inference does and the reading is written in before the
  term is hashed (§3.10). `let f x = e` is `Lam "x" e`.
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
  matching applications. Dimension and length arguments are erased at runtime,
  except where a value's shape or dimension comes from them alone (§8), and
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
| 0x05 | `Lam t` | `t` |
| 0x06 | `App f a` | `f`, `a` |
| 0x07 | `Let e b` | `e`, `b` |
| 0x09 | `Pow t n` | `t`, sint `n` |
| 0x0A | `Noise k l n` | one byte kind (0 bound, 1 stat), label, varint `n` |
| 0x0B | `Uncertain k l x err` | one byte kind, label, `x`, `err` |
| 0x0C | `Pack ts` | varint count, each `t` |
| 0x0E | `Cycle ts` | varint count, each `t` |
| 0x0F | `Proj t i` | `t`, varint `i` |
| 0x10 | cycle-variable placeholder | no payload; only in the ordering hash of §6.2, never in a stored term |
| 0x11 | `Con con args` | constructor reference, varint count, each argument |
| 0x12 | `Case s alts` | `s`, varint count, each alternative: constructor reference, varint `k`, (`k` hints in the storage encoding), body at depth `+ k` |

No other tag is written, and the decoder refuses any other.

A label is one byte (0 owner, 1 tag, 2 axes) and the text; the axes kind
stamps only the type a chart declaration mints (§3.9) and is never written
by the desugarer on a term, but decodes there as anywhere. In the *storage*
encoding (§7.4) every `Ref` is followed by the name the author wrote, and
every binder by its name hint; the canonical encoding, and so the hash, has
neither. The owner stamp is the full path of the enclosing definition
(§3.2.4), so the hash of a definition that declares uncertainty depends on
its name and its namespace; nothing else in the hash does.

A constructor reference is the 32-byte definition hash of its type and the
varint position of the constructor in it.

A declared type (§2.3) is hashed separately, from its own canonical encoding:
varint parameter count and one kind byte per parameter (0 type, 1 length, 2
shape, 3 dimension, 4 axis, 5 frame, 6 space, 7 role); varint constructor
count, and per constructor a varint field count and each field type; then
the label: 0 owner and the type name, or 1 and an empty text for
`structural`, or 2 and a chart's full path for the axis type its declaration
mints (§3.9: no parameters, one constructor with no fields, a label kind no
source declaration produces), or 3 and a space's full path for the type a
`space` declaration mints, or 4, a chart's full path and a byte, 1 for a
moving chart, for its frame type (§3.10, part F). Types use tags of their
own:

| Tag | Type | Payload |
|---|---|---|
| 0x21 | `Tensor σ δ` | shape, dimension |
| 0x26 | `a -> b` | `a`, `b` |
| 0x27 | variable | varint id (a parameter: 0 .. k-1) |
| 0x28 | `T a…` | 32-byte hash, varint count, each argument as a kind byte and a type, length, shape, dimension or axis |
| 0x2A | `Unit δ` | dimension (§3.10, U1) |
| 0x2B | `Point φ` | frame (§3.10, F4) |
| 0x2C | `Chart φ` | frame (§3.10, F4) |
| 0x2D | `Diff φ`, `Coords φ` | frame, then 0 for `Diff` or 1 and a dimension (`Coords`, dimension 1), the residual amount type until the space's shape is known (§3.10, F4) |
| 0x2E | `Quantity r δ` | role, shape, dimension: a quantity of a role variable (§3.10, U9); an amount is `0x21` and a unit `0x2A` |

A shape is 0 for `[]`, 1 then a length and a shape (a position with anonymous
axes), 2 and a variable id, or 3 then a length, an axis and a shape (a position
whose name slot is not anonymous, §3.9); an axis is 0 for anonymous, 1 and the
32-byte hash of a named set, or 2 and a variable id; a length is 0 and a
varint literal, 1, a variable id and a varint offset, or 2, a shape variable
id and a varint offset for `rank s + k` (§4.1); a dimension is a varint atom
count and per atom 0 and a base-dimension byte or 1 and a variable id, then
the sint exponent. A recursive occurrence of the type being declared is
`0x28` with the all-zero hash, so the definition never contains its own
hash. A length parameter has a companion axis parameter after the written
ones (§3.9). `Bool`, tuples and lists are `0x28` on the hashes of their
declarations (§2.3), which are therefore fixed by this encoding: `structural
data Bool = False | True` is no parameters, two constructors of no fields and
the structural label, and so on.

A frame (§3.10, F9) is its slot, 0 and the 32-byte hash of its minted frame
type or 1 and a variable id, then its axis and its space; a space is its
slot, 0 and the hash of its minted space type or 1 and a variable id, then
its shape, dimension and base axis. A declared type's argument of kind
frame is 5 and a frame slot, of kind space 6 and a space slot. A role
(§3.10, U9) is 0 for `Amount`, 1 for `Unit`, or 2 and a variable id; a
declared type's argument of kind role is 7 and a role.

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
names it. Both forms can be used in expressions. Named references search the
name's current binding and history through the usual namespace lookup, even
after the name is removed. Bare references search all stored terms. Missing
or ambiguous prefixes are errors; ambiguity reports include full hashes.
Named references cannot select a version that was never associated with that
name. They bypass local binders and new definitions in the same binding group.
The selected term's stored type determines its unit or chart role, rather than
the current name's flags. References to declared type constructors are not
term hashes and are outside this syntax.

A bare hash used as an argument is parenthesised: `f (#hash)`. For projection
from an ordinary historical tensor use `(v#hash).0`; `#hash.0` selects a cycle
member instead. A glued `name#hash` is a reference, while a separated `#label`
remains the uncertainty postfix. The name/hash syntax selects a Core reference,
not a permanent pin: stored dependents still follow the existing upgrade rules.
An accepted replacement is not itself rewritten during propagation. Thus
replacing `x = 5` with `x = x#old + 1` gives `6`, not `7`; other dependents
still upgrade, even if a dependent shares the replacement's hash. A reference
to a definition's own past is intentional and is not listed as a stale todo.

A reference into a cycle prints as `#hash.i`, and `:view` of a cycle
member shows that member's body with the other members by their current names.
Within one input, defining the same name twice is an error rather than a
rebinding: rebinding is something that happens between inputs. The same
applies to the standard library (§7.7), which is names like any other:
rebinding `astro.G` to a newer CODATA value with `:update --no-upgrade` leaves
every existing function pointing at the old `G#…`, `:dependents astro.G` lists
them, and `:upgrade astro.G` moves them.

Relabelling never changes a hash, with one exception: a definition whose
term carries an owner stamp, a `±`, `noise` or `gauss` written in it
(§3.2.4), and a nominal type (§2.3), are stamped with their full path.
`:rename` and `:move` of such a label, alone or as part of a namespace,
re-stamp it with the new path and re-hash it, so it has the hash its text
would have if entered under the new name. Then everything that mentions it
follows, dependencies first, as `:update` propagates: a type whose fields
use a re-hashed type, a definition that uses a re-hashed type's
constructors, and every dependent of a re-hashed definition, re-checked and
re-bound, with a cycle's other members and the type's constructor and
field labels moving with it. All or nothing: if anything would no longer
check, nothing changes. The report says what moved: `re-hashed data
mechanics.Body` for a type, `re-hashed lab.x #k1 -> #k5` for each moved
definition whose hash changed, `upgraded b #k2 -> #k6` for each dependent
outside the move. History keeps the old path on the old hash. (A cycle
re-stamped in place keeps its members' order, which re-entering its text
might not give: then the text gives another hash for the same cycle.)

Signatures (§4.8) are labels too, kept per name like the `unit` and
`chart` flags. `:rename` and `:move` move a signature with its name (a
re-hashed type it mentions is followed), `:unname` removes it, and `:alias`
does not copy it: an alias names the hash, which has no signature, so `f`
can be signed while its alias `g` is not. Rebinding a signed name to a new
version keeps the signature only if it holds of the new definition (§4.8).

### 7.3 REPL commands

```
Scratch and codebase (7.5)
:add                    store pending definitions whose names are new; conflicts refer to :update
:update [--no-upgrade]  store pending definitions, re-binding existing names, then propagate
:upgrade name           move dependents still on old versions of name to its current version
:todo                   pending definitions and stale references
:scratch                list pending definitions, a signature as `pending: area :: Shape -> Num (m^2)`
:forget name            drop a pending definition, and its pending signature
:edit [name|ns]         open the codebase but the library, a namespace (a library one included), or one definition or
                        type in $VISUAL or $EDITOR as source, and reconcile the saved file with the
                        codebase: add, update (with propagation), remove; all or nothing (below).
                        Without an editor, print the source instead: for one name, the definition
                        or data declaration ready to paste back, in a namespace block when it is
                        outside the current namespace (7.6)
:edit --file path [name|ns]
                        reconcile a file without opening an editor (one kept after an error)

Inspection
:ls [glob|namespace] [--all|--units|--charts|--types] [: type]
                   names with their types, sorted; alone, the current namespace's own labels,
                   then one line per namespace directly under it, `namespace si (799 names)`;
                   a word that names a namespace lists everything under it, relative to it, data
                   lines included; --all lists everything by full path; a glob (* anywhere, else
                   a substring; on the full path or its last segment), a kind, or a type query
                   whose lowercase unknown names are variables (no forall needed: a query is a
                   pattern), matched by unification both ways, searches everything; a signed
                   name shows, and matches, its signature (4.8); types print headed by forall;
                   --types lists a chart's minted frame as `frame lvlh` and a space as
                   `space GCRS = Vec 3 m`; minted axes go by their chart's name (3.9, 3.10)
:type e            inferred type scheme of e, headed by forall when it has variables
                   (forall a. a -> a); a signed name's signature, as its uses see it (4.8);
                   the type of `it`, so a value that is not a function has anonymous axes
                   where nothing fixes them (3.9)
:hash name         current ref of name
:names #hash       every name that points at the hash (current or historical)
:history name      refs the name has pointed at, newest first
:view name         pretty-print the term with refs rendered as in 7.2; for a type, its declaration;
                   a chart with its keyword, `chart degC on ITS90 at 273.15 K`, a space as
                   `space ITS90 = Num K` (3.6, 3.10); a name the uses offer as several
                   shows each after a `-- full.path` line, types first and then by path
                   (`:view TT` shows `time.TT`, a space, and `si.TT`, the teratesla).
                   :hash, :history, :core, :lint and :dependents take the one definition
                   among them, and list them when there are several:
                   "`h` is both `physics.h` and `time.h`; write one of them"
:core name         print the Typed Core (5.3) with every annotation
:lint name         re-run lint on a stored definition and print its type(s)
:dependents name   definitions whose terms reference the current ref of name
:alias new old     point new at old's current ref; for a namespace, give every label under old
                   the same label under new
:unname name       remove the label (of a definition, a type or a constructor; .f for a field); the term stays;
                   for a namespace, every label under it, with the count
:rename old new    relabel a definition, type, constructor or field, or every label under a namespace
                   (7.6); history keeps both names; all or nothing
:move name… ns     :rename each name (a label or a namespace) to ns.<its last segment>

Namespaces (7.6)
:namespace [path|.] show or set the current namespace (a full path); . is the root
:uses              list the uses in effect: the codebase's stored ones, marked (stored), then the
                   session's; a `use` statement adds one for the session
:use path [as a]   add a stored use, kept in the codebase (7.7)
:unuse path        drop a use, by its path or its alias: a stored one when there is one (and say
                   so), else the session's
:stdlib upgrade    take the shipped standard library's newer definitions (7.7)

Session
:set precision n   significant digits printed; working precision is n + 4 (3.2.8)
:set sigma k       confidence multiplier for comparisons on statistical values (3.2.9)
:set nonlinear p   percent of the first-order σ a second-order statistical term may reach
                   before a value is marked non-linear (3.2); default 1
:prefer [unit]     print values of the unit's dimension in it (3.2.12); alone, list preferences
:unprefer unit     remove that preference
:set unicode on    pretty-print with unicode spellings (2.8); off (the default) for ASCII
:set               list the settings: precision, sigma, unicode
:exact e           raw rational, or midpoint and nudge list
:budget e          error budget (3.2.6)
:covariance e      covariance (or variance) of the statistical nudges, and the bound box (3.5)
:load file         enter a file into the scratch as one binding group; its `use`s last for the file
:export [ns] [file] the stored codebase but the library, or the namespace ns (a library one included), as source
                   :load reads back (7.4); to the file when one is given (a word that is no
                   namespace is the file if it has a / or a ., else refused as a misspelling)
:colour [on|off]   colour the REPL's output; alone, say whether it is on (a REPL-level setting, below)
:quit
```

**Editing in place.** `:edit` is a round trip through a text editor. It
has three forms, and they work alike: `:edit` alone takes the stored
codebase except the library's namespaces (what `:export` writes),
`:edit orbital` takes a namespace (`:edit si` the SI part of the library), and `:edit
period` takes one definition or `data` type, with the other members of
its cycle when it has one (a member alone would enter again as another
term).

1. **Export.** The scope is written to a new temporary file,
   `metron-edit-….metron` in `$TMPDIR` (else `/tmp`), in the `:export` format
   (§7.4): the stored `use`s as `use` lines, then `namespace` blocks by
   full path from the root. A header comment says what saving does. The
   file is read from the root with no `use` of the session, as it was
   written, so the current `:namespace` and the session's `use`s do not
   change what it means.
2. **Edit.** The REPL runs `$VISUAL`, else `$EDITOR`, through `sh -c` (so
   `EDITOR="emacs -nw"` works), gives it the terminal, and waits.
   haskeline holds the terminal only while it reads a line, so the prompt
   is sane afterwards. A non-zero exit, or a file saved unchanged, changes
   nothing, says so (`nothing to do: the file was not changed`), and
   deletes the file.
3. **Reconcile.** The saved file is entered as one binding group on top of
   the codebase, as the scratch is (§7.5), and compared with the codebase
   by full path, over every kind of label: definitions with their `unit`
   and `chart` flags, types, constructors and fields.
   - *Added*: the file defines the label and the codebase did not have it.
   - *Updated*: the file binds the label to another reference. When the
     old term, with the group's new references and a replaced type's
     constructors put in, is the new term, only what it uses moved, and
     it is reported as *upgraded* instead.
   - *Removed*: a label of the scope that the file does not define, removed
     as `:unname` removes it; history keeps the term. Nothing is removed
     for one name. A definition moved to another `namespace` block is a
     removal and an addition, because a label is its full path.
   - *Unchanged*: everything else. The same text under the same path gives
     the same hash, a `±` definition and a nominal type included, since
     their owner stamp is the full path (§3.2.4).

   A definition outside the scope that the file defines is added or
   updated in the same way. Then propagation moves the dependents outside
   the file to the new versions, as `:update` does, and also the
   definitions that build or match a replaced type's constructors (matched
   by name). One that no longer checks is left on its version with the
   reason. A dependent of a removed definition keeps its reference and is
   reported stale. A type outside the file whose fields use a replaced
   type keeps the old one, and is reported.
4. **All or nothing.** These refuse the edit and change nothing: a parse,
   type or namespace error (with its excerpt, at the line in the file), an
   expression in the file, a file that no longer defines the one name
   (``the file no longer defines `area`; use :unname to remove it``), a
   file that would remove every label of the scope, such as an emptied
   buffer (``the file defines nothing in `orbital`; if you mean to remove
   it all, use :unname orbital``), a definition named `it`, and a
   pending scratch that would no longer check on top of the result. After
   an error the file is kept, and the REPL prints its path and the command
   that resumes from it: `:edit --file /tmp/metron-edit-1234-0.metron orbital`.

The report reads as `:update`'s: `added data T` or `updated data T`,
`added x`, `updated x #old -> #new`, `removed x` (and `removed data T`,
`removed constructor C`, `removed field f` for what an edited type left
behind), `upgraded y #old -> #new`, `left y on #r: why`, `left data P on
the old version of T`, `left y stale: it uses x#r, which was removed`,
`signed f` and `unsigned f` for a signature line (§4.8) added, changed or
deleted on a definition the file keeps; or `nothing changed`. A signed
definition is written with its `f :: type` line just before its `let`.

```
> :edit orbital                          -- x = 3 becomes x = 4; spare is deleted
updated orbital.x #k1 -> #k5
removed orbital.spare
upgraded orbital.y #k2 -> #k6            -- in the file, its text unchanged
upgraded mechanics.useY #k3 -> #k7       -- outside it, by propagation
```

`:edit --file path [name|namespace]` reconciles a file without opening an
editor: one kept after an error, or one a script wrote. Without an editor
(`metron -i`, one-shot mode, or neither `VISUAL` nor `EDITOR` set), `:edit`
prints the source it would have opened and a note that says why: for one
name, the statement it always printed, spelled for the current namespace
and ready to paste back (a pending definition too); for a namespace or the
codebase, the export. In one-shot mode the note goes to stderr, so the
source stays pasteable.

With `:set unicode on`, printed values, `:type`, `:view`, `:edit`, `:exact`,
`:budget`, `:covariance` and the `:prefer` message use these spellings from
the table in §2.8, and nothing else changes except the echo described below:

| ASCII | Unicode | Where |
|---|---|---|
| `^2` `^-1` | `²` `⁻¹` | unit exponents (`9.81 m s⁻²`, `5 km h⁻¹`), dimensions in types (`Num (m/s²)`), powers in `:view` (`x²`) |
| `->` | `→` | function types, lambdas and case alternatives |
| `\` | `λ` | lambdas: `λx → x² + 1` |
| `<=` `>=` `/=` `\|\|` | `≤` `≥` `≠` `∨` | operators in `:view` |

`*` stays `*`, because `×` is the cross product; `/`, `&&`, `sqrt`, `forall` and
names such as `pi` and `deg` keep their ASCII spelling (`∀` reads as `forall`
but is not printed). `√` would change the
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
- after `:load` and `:edit --file`, a file name;
- after a `.` glued to a value, a record field name (`b.ma` gives `b.mass`);
- elsewhere, a name the session sees (definitions, units, types and
  constructors, pending ones included) or a keyword.

The standard library has many hundreds of names, so a short prefix can list many
candidates.

**Unicode by name.** A backslash, a name, then TAB enters a character, as
in Julia: `\mu` gives `μ`. When the typed name is a whole entry, it is
replaced, so `\pm` gives `±` although `\pms` exists. Otherwise TAB lists
the entries that start with it. The table is in `Metron.Unicode`:

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
is not `dumb` and `NO_COLOR` is not set. The theme uses only the 16 ANSI
colours, so it shows on any terminal. It has no dim text, because some
terminal themes do not show dim text:

| what | colour |
|---|---|
| an error's `error at` line and message | red |
| an error's carets | bold red |
| notes: `pending:`, `added`, `updated`, `nothing …`, the namespace lines of a bare `:ls`, `kept`, `stored use`, `(input abandoned)`, the `≡` of the unicode echo | bright black (grey) |
| comments, `-- …` and `{- … -}` | bright black |
| keywords: `let unit chart space on from data case of in where if then else to true false at namespace use forall`, and `structural` before `data` | magenta |
| numbers and superscript powers | plain |
| units, the SI base units and charts | cyan |
| type names, constructors, the built-in heads `Num Vec Mat Tensor Point Chart Bool` | yellow |
| `#hash` references and `#label` tags | bright black |
| operators, brackets, `->`, `\`, `=`, `:` | plain |
| other names: definitions, variables, fields | plain |
| the prompts `> ` and `… `, and the `> ` of the scripted echo | bold |

Highlighting follows the lexer. The REPL lexes each printed line of source
text or value and colours each token by its span. A comment is the text
between tokens that is not blank. The highlighted lines are the `≡` echo,
`:view` and `:edit` output, `data` declarations, the source excerpt of an
error, values, `:type` output, the type in a `name : type` line of `:ls`,
and the input echo of `metron -i`. An error's carets stay under the excerpt,
because colour codes take no columns. The name in a `name : type` line
stays plain. Its `unit` or `chart` is a keyword.

Some details of the rules:

- In a type, a name is cyan only inside `[…]`. So a type variable such
  as `m` or `g` stays plain in `(g → m) → {g}`.
- A variable that a `forall` on the line binds stays plain inside `[…]`
  too, since it shadows the unit: `s` in `forall s. Num s`.
- In a `data` declaration, the type name and the constructor names are
  yellow even before the session knows them.
- A name that a line binds (between `let`, `where`, `\`, `of` or `;` and
  the next `=` or `->`) is a variable on that whole line. So `s` and `h`
  stay plain in `\s -> case s of Rect w h -> w * h`. The highlighter does
  not resolve scope.
- A `…` in a value lexes as a space, and `#hash.1` lexes as one token.

If a line does not lex, its kind decides the colour instead. A value then
gets its trailing unit cyan, a type turns yellow, a note turns grey, and
an excerpt stays plain. A line also counts as not lexing when NFC would
change its length or when it has a tab. In those cases the spans would
not index the printed text. Colour only adds escape codes. Remove them
and the text is the same as without colour.

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
> data Shape = Circle (Num m) | Rect (Num m) (Num m)
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

`metron -i` reads continuation lines in the same way, so a piped script can
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
metron                     REPL
metron 'expr'              one-shot: print the value, exit 0; on error print to stderr, exit 1
metron -f file.metron          load a file as a binding group, print bare expressions
echo 'expr' | metron       same as -f on stdin
metron --codebase DIR …    use an explicit store
metron --merge OTHER       merge the store at OTHER into this one, leaving OTHER as it was
```

A codebase on disk is a directory:

```
format             "metron codebase 11": the store's format version
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
                     <unix time> chart <name>              -- a chart flag (3.6)
                     <unix time> unflag <name>              -- a let took over a unit or chart name
                     <unix time> prefer <unit text>
                     <unix time> unprefer <unit text>
                     <unix time> type <name> <hex hash>          -- a type label
                     <unix time> con <name> <hex hash>.<i>       -- a constructor label
                     <unix time> field <name> <hex hash>.<i>.<j>  -- a record field label
                     <unix time> use <path> [as <alias>]          -- a stored use (7.7)
                     <unix time> unuse <path> [as <alias>]
                     <unix time> sig <name> <type>                -- a signature (4.8)
                     <unix time> unsig <name>
history            the REPL's line history
```

A `sig` line holds the signature as text that reads back at the root
whatever came after it: ASCII, declared types by their absolute paths
(`.Shape`, so the stored `use`s cannot change what it means), and its
variables bound by `forall` (§4.8), so a variable shadows a unit of its
name: `sig same forall s d. Tensor s d -> Tensor s d`. On replay it is
parsed and converted as a written signature is (§4.8), a sized binder
sized. It is kept when its name is bound to a definition it holds of;
otherwise it is skipped with a note. Sig lines come after every other line
of a sync, so the labels they name exist.
`unsig` is written when a name loses its signature, whether or not it stays
bound.

Types and Typed Core are not stored; they are recomputed on load by
typechecking and linting each term, dependencies first (cheap: the standard
library's 800 definitions take 30 ms). Terms are only ever added, so two stores never
conflict on terms; the log is the one thing with order, and merging two stores
is concatenating their logs and sorting by time, last writer winning per name.

`metron [--codebase DIR] --merge OTHER` does that, into the store that `metron`
would otherwise use. Both stores are opened as usual, OTHER first, so a store
of an older format is refused (below), and so is a directory that is not a
store; either is left untouched. Every file in OTHER's `terms/` and
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

The user store lives at `$XDG_DATA_HOME/metron/` and is what the daily calculator
uses. A project-local `.metron/` directory, found by walking up from the current
directory, shadows the user store, and `--codebase DIR` names one explicitly;
`--no-codebase` runs in memory. iapetus commits its `.metron/` to git.

**Export: the text form of a store.** `:export [ns] [file]` writes the
stored codebase, or the namespace `ns`, as source that `:load` reads back:
in a fresh session, `:load file` then `:add` gives the same labels on the
same hashes (`names`, `typeNames`, `conNames`, `fieldNames`, `units`,
`charts`, `signatures`).
Each namespace is a `namespace` block, nested as
the paths nest, with root definitions outside any block. Each definition
is rendered as `:edit` renders it (`let name = body`, `unit name = …`,
`space Name = type`, `chart name params on parent` with its clauses when set
(3.8, 3.10), `data` declarations with their field names, and a
signed definition's `name :: type` line just before it, spelled for its
block, with its `forall`, §4.8). The standard library's
namespaces are not exported unless one is asked for (`:export si`): a codebase that
reads the export is seeded with it already. The codebase's stored `use`s
(§7.7) head the export as `use` statements, the six of a seeded codebase,
and every name is spelled for them and for its block (§7.6): a library
term a user definition references prints as `km`, a name the block shadows
gets its leading dot (`.km` for a root `km`), and so does a root name that
a stored use also offers, since a `use` in a file comes before the root.
So the text means the same in any codebase seeded with the library,
whatever its stored uses. Types come first, each after the types it uses, since `data`
declarations are entered in order; then the terms, each after what it
references, a cycle's members together, and among what is ready the ones
in the same namespace as the last, so few blocks are reopened. `:export
orbital` exports that subtree as `namespace orbital …`, so loading it
elsewhere lands it in the same place; an empty codebase exports nothing;
the pending scratch is not exported, and a closing comment (or, for a
file, a note) says so.

What does not round-trip, and why: a definition that refers to a version
no name points at (after `:update --no-upgrade` and an `:unname`) cannot
be written as source, so the export refuses and names it; a definition
with a `±` and a nominal type are stamped with their full path (§3.2.4,
§2.3), which `:rename` and `:move` keep up to date by re-hashing (§7.2), but
a definition whose stamp does not match its path (a second label on it)
gives a new hash when its export is re-entered; two labels
on one reference export as two definitions, which hash alike only when the
body declares no `±` and is not recursive (the second refers to the first
by name instead of being a member of its cycle); a type or constructor
that a definition uses but no label names any more prints as a hash and
does not read back; a library name the user rebound or unnamed under its
namespaces is not exported with the rest (`:export si` writes that part as
the codebase has it, which needs `:update` rather than `:add` where it
differs from the seed); history, preferences and the `use`s of the session
are not part of the export. This answers the question of §11 for iapetus:
the binary `.metron/` store stays the source of truth for history and
hashes, and an export beside it is the reviewable text, diffable in git
and enough to rebuild the current labels.

**Seeding.** The standard library lives in the store like everything else
(§7.7). A store that does not exist yet is created and seeded: the
library's terms are written, then its labels as ordinary `bind`, `unit` and
`chart` lines and its six stored `use`s, all stamped with time `0`. Time 0 sorts
before every line of the user's, so a merge can never let the seed override
the user, and the seed's lines are the same in every store, so merging two
seeded stores brings nothing across for the library. The format file is
written last, so an interrupted seeding is seeded again. A store is then
loaded on top of the empty codebase, with no prelude step: an empty store
really is empty, and the second start of a new store reads the library
from disk. `--no-codebase` seeds the same library in memory. Each successful input is written through immediately: new terms first,
dependencies before dependents, then the log lines, so an interrupted session
never leaves a name pointing at a missing term. A term that fails to decode,
fails to typecheck, or is named but missing is reported as a note at start and
skipped; the rest loads.

**Formats.** A store opens only at the format this build writes, 12. A
store of another format is refused with one line, and nothing in it is
touched: "<path>: this codebase is format N; this metron opens format 12". A
format file that says anything else is refused as not a metron codebase.

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
  is a workspace, not a scope. A pending definition is known by its full path,
  and keeps the scope it was written in (its namespace and the `use`s then in
  effect, §7.6), so re-entering the scratch resolves it as it did. After
  `:namespace orbital`, `let x = 1` is `orbital.x`; `:scratch`, `:todo`,
  `:add` and `:update` print names as the current scope spells them
  (§7.6), so it shows as `pending: x` there and `pending: orbital.x` at the
  root. A signature (§4.8) is a pending entry of its own beside its
  definition's, `pending: area :: Shape -> Num (m^2)`: a later input's
  signature replaces it (``replaced pending signature of `area` ``), a later
  `let area` is checked against it, and `:forget area` drops both. A
  pending signature for a stored definition alone is stored by `:add` or
  `:update` as `signed area`.
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
  forgotten. `:edit` opens a definition, a namespace or the codebase in an
  editor and reconciles the saved file with the codebase (§7.3), adding,
  updating with propagation, and removing; without an editor it prints the
  source, for the scratch.
- **`it`**, the last expression (§7.3), is never stored. It is not in the
  scratch, so `:add` and `:update` do not see it, and nothing reaches the
  codebase or the store through it. A definition that mentions it is refused
  with "`it` is the last result and cannot be stored; paste its definition
  (:view it) instead", and so is a definition named `it`. `it` keeps the
  terms it was checked against, so replacing or forgetting a pending
  definition it used does not break it.

`:add` and `:update`, and `:edit`, which does both from a file, are the only ways
a label moves to new content. History records
every binding, `:view` shows exactly which version a definition uses, and the
semi-automated upgrade is the propagation report: what moved, and what did not
and why.

---
### 7.6 Namespaces

A name is a dotted path, `orbital.kepler.period`, and nothing else changes: a
namespace is a prefix on a label. Terms, hashes and the store do not see it,
since a `Ref` carries only a hash and, in the storage encoding, the name as
written (now the full path it resolved to); the one exception is the owner
stamp of a `±` definition or a nominal type, which is its full path (below).
Moving `period` under `orbital` is a relabelling (§7.2), so history keeps
the old name and nothing is re-hashed, unless `period` is stamped.
Types, constructors and fields are labels too and move the same way, and so
do the `unit` and `chart` flags. The standard library's units and
constants live in namespaces by domain (§7.7) and the stored `use`s reach the
common ones: `5 km` is `si.km`.

**Blocks.** `namespace` opens a block of statements, laid out as a `where`
block is (§2.2): it opens at the first token after the path, which must be
indented further than the `namespace` line. The block holds `let`, `unit`,
`chart`, `data`, `use`, expressions and nested `namespace` blocks, and what
it declares gets its path as a prefix: definitions, units, charts, types,
constructors and record fields alike.

```
namespace orbital
  let mu = 398600.4418 km^3/s^2
  let period a = 2 * pi * sqrt (a^3 / mu)    -- mu is orbital.mu
  data Body = Body {mass :: Num kg, dist :: Num m}
  namespace kepler                           -- nests: orbital.kepler.*
    let anomaly e m = m + e * sin m
use orbital                                  -- bare names from orbital.* resolve
use orbital.kepler as k                      -- k.anomaly
let g0 = 9.80665 m/s^2                       -- root
```

The statements of the blocks belong to the input's one binding group, so
dependency analysis and cycles work across them: it runs on full paths, and
`period` inside `namespace orbital` depends on `orbital.mu` when the group
defines it.

**Resolution.** A name written in an expression, a type or a command
resolves in this order:

1. a local binder (a lambda parameter, a `let`, a pattern variable);
2. the current namespace: `period` inside `namespace orbital` means
   `orbital.period` when that exists (in the group or the codebase); an
   enclosing namespace is not searched, so inside `orbital.kepler` the
   name `mu` is not `orbital.mu` (write that, or `use orbital`);
3. the `use`d namespaces: `u.x` for each `use u`, and `u.y` for `k.y` under
   `use u as k`. Two of them offering the name is an error, not a choice:
   "`x` is both `a.x` and `b.x`; write one of them";
4. the root, which is where every name without a dot lives;
5. the codebase's stored `use`s (§7.7), the six of a seeded codebase (`std`, `linalg`, `si`, `time`, `angle`,
   `temperature`),
   with the same rule against two of them offering the name.

A full path written out, `orbital.period`, resolves as itself at the root
step, so it works from anywhere unless a nearer namespace has the same path
under it. A leading dot writes an absolute name: `.km` is the root's `km`
and `.orbital.period` the full path, whatever is current or used. At the
root, step 2 is skipped, so a `use` of the session or a file takes
precedence over a root name of the same spelling, while a root name takes
precedence over a stored `use`: `let c = 3e8 m/s` at the root shadows the
library's `physics.c` (after `:use physics`) without ceremony, and
`physics.c` still reaches it. Each kind
of label resolves among its own kind: definitions and constructors share
one set, types and fields have theirs.

A `use` path is always a full path (a leading dot is allowed and means the
same). A `use` applies to the statements after it in its block and in the
blocks inside it. A top-level `use` typed at the REPL lasts for the session
(`:uses` lists them, `:unuse` drops one); a file read with `:load` keeps its
own to itself. Neither `namespace` nor a `use` statement is stored: a
stored term holds full references, so no reader of the codebase needs
imports to make sense of it. The one exception is the codebase's stored
`use` list, the six at seeding (§7.7), kept as log lines and changed with
`:use` and `:unuse`.

**The dot.** `b.mass` is a field access and `v.0` a projection, so
`orbital.period` lexes as "field `period` of `orbital`". The desugarer
decides (§2.10): for a chain whose head is not a local binder, the longest
dotted prefix that resolves to a definition or a constructor is a qualified
reference, and the rest is field access. That rule is unambiguous because
**a name is never both a label and a namespace**: declaring `let orbital = …`
while any `orbital.*` label exists is refused ("`orbital` is a namespace; a
definition cannot have its name"), and so is declaring anything under
`period.` while `period` is a label ("`period` is a definition; it cannot
also be a namespace, as `period.x` would make it"). The rule covers labels
of every kind, it is checked for a whole binding group and for `:alias`,
`:rename`, `:move` and `:namespace`, and it means a namespace cannot be
named like a definition (`namespace si.km` is refused).

*Fields.* A field written after a dot is a bare name and resolves through
the scope only (`.mass` is `orbital.mass` inside `orbital`, or with `use
orbital`). From elsewhere, a field of a type in another namespace cannot be
written by path; `use` its namespace. A record built with a constructor,
`orbital.Body {mass = …, dist = …}`, takes its field names as that
constructor's own, by their last segment, from anywhere. Records print
their fields so.

**Stamps see the namespace.** A definition's declared uncertainties are
labelled (§3.2.4) with its full path, and a nominal type is stamped (§2.3)
with its full path, so `lab.offset = 1 ± 0.1` and `field.offset = 1 ± 0.1`
are two terms and two measurements, `lab.offset - field.offset` carries
both nudges, and `a.Body` and `b.Body` with the same fields are two types.
Everything else is the same term wherever it is written: `let q = 1 m` has
one hash at the root and in any block. The other side: renaming or moving
a stamped definition re-hashes it, which `:rename` and `:move` do (§7.2),
and the library's `astro.G` is not the hash a root `G` of the same text
has.

**Printing.** A name prints as Unison prints it: the shortest spelling that
resolves back to the same label in the current scope, trying in order the
last segment alone, the path relative to the current namespace, the path
relative to each `use` (under its alias, `k.anomaly`; the session's, then
the stored ones), the full path, and,
only when the full path itself would resolve to something else here, the
absolute `.full.path`. So inside `namespace orbital` with no `use` of the
session, `orbital.period` prints `period` and the library's `si.km` prints
`km`; with `use orbital` at the root, `orbital.period` prints `period`; with
`use a` and `use b` both offering `x`, `a.x` prints `a.x`; a block that
defines its own `km` refers to the library's as `si.km`, and to a root
`km` as `.km`; and after `:unuse si`, `5 si.km` prints `5 si.km`. At the
root with no `use` of the session, every root name prints as itself, as
before namespaces, and so does every library name no root name shadows. The rule
(`Metron.Resolve.shortestName`) is used for `:view`, `:edit`, `:core`, values
and their units, types and constructors (through the type namer), `:ls`
outside a namespace listing, `:names`, `:dependents`, and the notes
`pending:`, `added`, `updated`, `upgraded`, `left` and `stale:`. So after
`:namespace orbital`, `let x = 1` shows as `pending: x`, and at the root as
`pending: orbital.x`.

**Commands.** A namespace is an object: wherever a command takes a name, a
namespace path means everything under it, and the command says how many
labels it touched. Names given to commands are relative to the current
namespace, go through the `use`s, or are absolute with a leading dot (but
`:unname .f` keeps naming the field `f`).

```
:namespace orbital           -- single REPL lines now land under orbital; :namespace . is the root
use orbital as o             -- for the session; :uses lists, :unuse orbital drops it
:ls orbital                  -- the namespace's labels, relative to it, data lines included
:rename orbital.period orbital.T    -- one label: renamed `orbital.period` to `orbital.T`
:rename orbital mechanics    -- every orbital.* label of every kind: renamed the 5 labels under …
:move period orbital         -- period becomes orbital.period; :move orbital.kepler mechanics
                             -- gives mechanics.kepler.*
:alias o2 orbital            -- every orbital.* label also as o2.*
:unname orbital              -- removed the 5 labels under `orbital`; :history name still finds them
```

`:rename`, `:move` and `:alias` of a namespace are all or nothing: a new
path that is already a label of the same kind ("`x` is already a label;
nothing was changed"), two names moved to one path, or a path that breaks
the namespace rule refuses the whole change. They are written to the store
as the existing `bind`, `unname`, `type`, `con`, `field`, `unit` and `chart`
log lines, beside the new term and type files of anything re-stamped (§7.2). `:edit` of a definition
outside the current namespace prints it inside a `namespace` block, with
its names relative to that block, for pasting at the root.

**Open.** Whether `:ls` shows more of the tree than one level; whether a
field should be reachable by path from outside its namespace.

### 7.7 The standard library

The prelude became a standard library that lives in the codebase like
everything else. It used to be entered in memory at every start with the
store's log replayed on top; that two-layer model kept `:ls` hiding 800
names, kept `:edit`, `:rename` and `:export` from touching units, and made a
prelude change rebind names behind the user's back. Now:

- **Seeding.** A codebase that does not yet exist is created with the
  standard library entered as one ordinary group of sibling `namespace`
  blocks, one per domain (the layout below: `std.map`, `linalg.cross`,
  `si.km`, `time.hr`, `temperature.degC`, `astro.G`, …), the source of
  `Metron.Prelude.stdlibSource`. The second labels on one term
  (`Metron.Prelude.stdlibAliases`: `si.newton` on `si.N`'s term, `time.h` on
  `time.hr`'s) are then bound as `:alias` binds them, a unit's alias a
  unit. The terms and the `bind`, `unit` and `chart` lines are written like
  any other, with six stored uses, `std linalg si time angle temperature`
  (§7.4 has the store's side: the seed's lines are at time 0). The second
  start reads it from disk; nothing is entered in memory first.
  `--no-codebase` seeds the same library in memory. A definition is the
  term it is written as, wherever it lives: `si.N`, `time.min` and
  `std.map` are the terms `N`, `min` and `map` would be at the root, and
  `si.km`, written
  `kilo * 1 metre`, has its own. One with a `±` is
  stamped with its full path (§3.2.4), so `astro.G`, the bodies of
  `astro.iers2010` and `astro.wgs84.earth` (its J2), and the solvers of
  `astro.kepler`, which declare their truncation error, have hashes of
  their own too.
- **Nothing is special afterwards.** The library is names in the database.
  `5 km` resolves through the stored `use si` and prints `5 km`; `:ls`
  alone lists the root's own names and one line per namespace, `namespace
  angle (6 names)` to `namespace time (12 names)`, sorted; `:ls si` the
  SI, `:ls --all` everything by full path; after `:use physics`, `let c =
  3e8 m/s` shadows `physics.c` without ceremony, since a root name comes
  before a stored `use` (§7.6), and `physics.c` still reaches the
  library's; `:rename time.hr time.hour` (then `3 hour`), `:unname
  astro.AU` and `:edit si.km` all work; `:export` leaves the library's
  namespaces out, and `:export si` writes that one.
- **A stored `use`.** A `use` statement lasts for the session (§7.6). The
  codebase also keeps a list of stored uses, the six from seeding, written
  as log lines (`<time> use si`, `<time> unuse si`) and replayed with the
  other labels. They resolve after the root, last of all, and two of them
  offering a name is an error, as for any uses. `:uses` lists them first,
  marked `(stored)`, then the session's. The rule for changing them is the
  one the commands already had, plus one command: `:use path [as alias]`
  adds a stored use (a `use` statement stays the session's); `:unuse path`
  removes a stored use when one matches the path or alias, and says so
  (`removed the stored use si; :use si puts it back`), and otherwise the
  session's. A change to the stored uses is refused when the pending
  scratch would no longer check without it. After `:unuse si`, SI names
  need their path (`5 si.km`); after `:unuse linalg`, so does `×`, which is
  the library's `linalg.cross`.
- **Upgrading** is an open question in general (how a definition in one
  codebase takes a newer version from another). For the library there is a
  sketch, `:stdlib upgrade`: the shipped library's labels in its namespaces
  against the codebase's. A name the codebase has never had is `added`,
  and so is a type, constructor or field label it has never had (`added
  data linalg.Cov2`, its constructor and fields with it; a type label the
  codebase already has is left as it is); a name whose binding is still the
  one it was seeded with (its history is that one entry) and whose
  shipped version differs is `updated`, and its dependents are upgraded as
  `:update` does; a name the user rebound or unnamed is `kept` (the user's
  wins). "Never touched" is read off the history because the codebase does
  not know which versions earlier libraries shipped, so a name moved by an
  earlier upgrade counts as the user's: the honest limit of a sketch.
  `--merge` is the wrong tool here: its last-writer rule would override the
  user's edits.
- **Base units stay primitives.** `m`, `kg`, `s` and the other base symbols
  are not names (§3.2.12); they need no namespace, cannot be renamed and
  are available everywhere. `si.metre` and the other spelled-out names are
  units defined as them (`unit metre = m`), which the prefixed units are
  written from.
- **One library.** Only the current library is in the build.

- **The built-in types.** `std` begins with `structural data Bool = False |
  True`, `structural data Pair a b = Pair a b` and `structural data List a =
  Nil | Cons a (List a)`, written exactly as the compiler holds them
  (§2.3), so entering them gives the compiler's hashes: `std.Bool` is the
  type of `true`, and `:view std.List` prints the declaration. The labels
  only name them: `true`, `(1, 2)` and `{1, 2}` print by hash, so renaming
  or unnaming `std.Bool` changes how `Bool` is named in `:view` of a
  declaration and nothing else, and the language works the same in a
  codebase without them. Under the stored `use std`, `True`, `Pair 1 2` and
  `Cons 1 Nil` are the constructors. The larger tuples' types (`(a, b, c)`)
  are known to the compiler but named by no library.

Consequences: the store's format is 6 (an older store is refused, §7.4); the loader
enters no prelude, so an empty store really is empty; the test suite's
"session with the prelude" became "a seeded session", the same thing by
another route.

#### Layout

The library is split by domain into sibling namespaces, each a `namespace`
block in the seed source, with the basic functions alone in `std`. The
counts are labels, as `:ls` counts them (aliases and record fields
included; a nested block's labels count in its top namespace), 981 in all:

| namespace | contents | labels | stored `use` by default |
|---|---|---|---|
| `std` | the types `Bool` (`False True`), `Pair` and `List` (`Nil Cons`), the compiler's own declarations; the structural functions `fst snd map filter foldr foldl foldl' length reverse zip range` | 18 | yes |
| `linalg` | `ε levi cross trace vimap`; the rotations `e1 e2 e3 rotx roty rotz dual axisAngle rotation euler313` (§3.3), `rotateVec rotateCov` (§3.9); the record `Cov2` with its fields `rr rv vv`, and `jointCovariance propagateCov2 innovationCov2 gain2 updateCov2 inChartCov2` (§3.7, §3.8) | 27 | yes |
| `si` | the spelled-out base units `metre second kilogram ampere mole candela radian`; the 24 prefixes as plain numbers, `quetta` to `quecto` (`let kilo = 10^3`); the 22 coherent derived and accepted units by symbol (`N J W Pa Hz C V Ω F S T H Wb lm lx Bq Gy Sv kat g L t`), each with its name as an alias on the same term (`newton`, …, `ohm`, …, `gram`, `litre`, `tonne`); the 699 prefixed units, each written from the prefix's name (`unit km = kilo * 1 metre`, `unit kPa = kilo * 1 Pa`), with `kohm` and the other prefixed ohms aliases of `kΩ` | 799 | yes |
| `time` | `min hr day week year`, with `h` an alias of `hr` (`unit hr = 60 min`); the space `TT` (Terrestrial Time) with the charts `JD MJD J2000`, and the space `UTC` with the chart `unix`, no chart between them | 12 | yes |
| `angle` | `deg arcmin arcsec turn sr`, with `steradian` an alias of `sr` | 6 | yes |
| `temperature` | the space `ITS90`; the charts (temperature scales) `degC degF degR kelvin`, written with `chart`, `degR` a rescaling of `kelvin`; the steps `deltaC deltaF` | 7 | yes |
| `astro` | the units `AU pc ly` (`pc = 648000 / pi * 1 AU`, `ly = physics.c * 1 time.year`) and `G`; the record `State` with its fields `epoch pos vel`, and `velocityIn stateFrom` (§3.8); the record `Body` with its fields `mu radius flattening j2 rate`; and nested blocks: the constant sets `wgs84` (`earth`), `iers2010` (`earth moon sun`), `iau2015` (`earth sun jupiter`) and `de440` (`sun mercury venus earth moon mars jupiter saturn uranus neptune pluto`); `kepler` (45 labels: the record `Elements` with its fields `a e i raan argp nu`, the relations, the conversions, the anomalies, the solvers, propagation and the J2 rates); `maneuver` (12: the record `Transfer` with its fields `dv1 dv2 dv3 tof`, and `total hohmann biElliptic planeChange combinedChange rotationAngle phasing`). See "The `astro` library" below | 91 | no: `:use astro`, then `:use astro.kepler` or a set for bare names |
| `physics` | `c planck hbar k_B N_A e_charge g0` and the unit `eV`, with `h kB NA e` aliases of `planck k_B N_A e_charge`: `physics.h` is Planck's constant, the hour is `time.h` | 12 | no |
| `imperial` | `inch ft yd mile lb oz lbf psi mph`, exact by the 1959 yard and pound (`lbf = 1 lb * physics.g0`, `psi = lbf / inch^2`) | 9 | no |

Rules the seed is checked against, each by a test: no name is ambiguous
among the six default-used namespaces, for each kind of label; and a name
only in a namespace no stored use reaches (`astro`, `physics`,
`imperial`: `AU`, `G`, `c`, `planck`, `g0` and the rest) is not bare.
Both hold for the nested blocks of `astro` too: `earth`, `period` and
`Elements` are not bare until `:use astro.wgs84` or `:use astro.kepler`.
Base units stay primitives, available
everywhere, and a `data` type's dimension (`Num N`) names a unit through
the scope like any expression.

What the build settled that the plan left open:

- **Two left folds, as Haskell has** (decided by the owner, 2026-11-01).
  `std.foldl` stays lazy in its accumulator: `foldl (\_ x -> x) (1/0)
  (range 0 3)` is `3`, and an accumulator that is never used never fails.
  `std.foldl'` evaluates each step's accumulator before the next, through
  the primitive `seq a b`: `b`, once `a` is evaluated to a value and, for
  a number, a tensor or a point, every component (data only to its
  constructor). A component that fails keeps its error to itself, as
  elsewhere (§3.3): `seq [1/0, 2] 5` is `5`. `length` and `reverse` are
  written with `foldl'`, so `length (range 0 1e6)` runs in constant memory;
  `seq` is in tail position, so a strict fold also runs in constant stack.
  `'` is an identifier character, so the name is spelled as in Haskell.
- **`kelvin` is the absolute temperature scale** (`0 kelvin to degC`),
  so `K` has no spelled-out unit name in `si`: a name is one label,
  and two default namespaces offering `kelvin` would be an error. The
  prefixed kelvins are written from the symbol (`unit mK = milli * 1 K`).
- **`in` is a keyword**, so the inch is `inch`.
- **The prefixes are powers of ten** (`kilo = 10^3`), not literals: a term
  is its content, so `let kilo = 1000` would be the same hash as a user's
  `let n = 1000`, and an `:update` of that would upgrade every `k` unit with
  it (§7.5).
- **The hour is `hr`, with `h` its alias**, and `physics.h` is Planck's
  constant. Both spellings of the hour work bare by default (`3 h`, `5
  km/hr`), each printing as written; after `:use physics`, a bare `h` is
  the usual ambiguity error, "`h` is both `time.h` and `physics.h`; write
  one of them", and `hr` is the way out. (The quantity rule lets an
  ambiguous name through so that this error, not "not a unit", is the one
  reported.)
- **`physics`'s defining labels are the long spellings** (`planck`,
  `k_B`, `N_A`, `e_charge`), and the short ones are aliases. The atomic
  mass unit `u` is not shipped yet.
- **`g0` is in `physics`**: standard gravity is a constant. There is no
  gauge-pressure chart (§3.10, F2).
- **References between blocks** are written by path (`angle.sr` in
  `lm = cd * angle.sr`, `physics.c * time.year`, `mile / time.hr`) or
  through a `use` inside the block (`physics` has `use si`), since the
  seed is entered before any stored use exists.

Writing `km` as `kilo * metre` instead of `10^3 * m`, and the hour as `60 *
min`, re-hashed every prefixed unit and the hour; this is accepted while the
language is in design. A store from before the split is refused, and is
recreated from its export (§7.4). Units as a type (§3.10, part U) re-hashed
every unit and every quantity again: `km` is now `kilo * 1 metre`, the hour
`60 min`.

#### The `astro` library (design; decided by the owner, 2026-11-01)

`astro` today is a stub: a few constants (`GM_earth` is the IAU 2015
nominal `3.986004e14`, not the WGS84 and EGM96 value most texts use), the
`State` record and two frame functions. It becomes a library of nested
namespaces, so that a user chooses a set of constants with a `use` and the
functions do not depend on the choice.

- **Constant sets are namespaces defining the same names.** A set holds
  `Body` values (below), and each value says its source in a comment and in
  its `:view`:
  - `astro.wgs84`, the WGS84 and EGM96 Earth that GPS and Vallado use:
    `earth`.
  - `astro.iers2010`, the IERS Conventions (2010): `earth`, `moon` and
    `sun`.
  - `astro.iau2015`, the IAU 2015 nominal values (Resolution B3):
    `earth`, `sun` and `jupiter`. These are exact by definition.
  - `astro.de440`, JPL DE440: `sun`, `moon` and the planets.

  `:use astro.wgs84` then makes `earth` the WGS84 Earth. Defining constants
  are exact, and measured ones carry their published uncertainty with `±σ`.
  No set is used by default.
- **A body is a record:** `data Body = Body {mu :: Num (m^3/s^2), radius
  :: Num m, flattening :: Num, j2 :: Num, rate :: Num (rad/s)}`, with exact
  zero where a source gives nothing. Every function that needs a body takes
  one, `period earth (7000 km)`, so a computation names its constants once
  and changing set is a `use`.
- **`astro.kepler`, two-body motion.**
  - Relations: vis-viva, period, mean motion, specific energy, angular
    momentum, and circular and escape speeds.
  - `data Elements = Elements {a, e, i, raan, argp, nu}`, elliptic or
    hyperbolic (`a < 0`, as Vallado writes it), with conversions to and
    from a position and velocity, including the circular and equatorial
    cases. Angles come from `atan2`, never from `acos` with a quadrant
    test. When a case cannot be decided because the value is too
    uncertain, it is an error.
  - Anomaly conversions: true, eccentric, mean, and hyperbolic.
  - A Kepler solver for each conic.
  - Analytic propagation, by advancing the mean anomaly, and J2 secular
    rates: the node, the perigee, and the sun-synchronous inclination.
- **An iterative solver's result is rigorous.** After a fixed number of
  Newton steps from a good starter, the solver adds its truncation error
  as a declared bound: for Kepler's equation `f(E) = E − e sin E − M`, with
  `f' ≥ 1 − e > 0`, so `|E − E*| ≤ |f(E)| / (1 − e)`. A result is therefore
  as rigorous as any other, and printing shows how converged it is.
- **`astro.maneuver`:** Hohmann, bi-elliptic, plane change, combined plane
  change and phasing, returning records such as `Transfer {dv1, dv2, tof}`.
- **The root `astro` keeps** the units `AU`, `pc` and `ly`, `G`, the
  `State` record, `velocityIn` and `stateFrom`. The Earth and Sun constants
  move into the sets.
- **Tests.** Every function is checked against a published worked example,
  cited (Vallado's *Fundamentals of Astrodynamics and Applications*,
  examples 2-1 to 2-6 and those of chapter 6, or Curtis), and the
  conversions round-trip.
- **Second build:** time (TAI and GPS charts, leap seconds, GMST and the
  Earth rotation angle), frames (`GCRS`, a moving `ecef`, ENU and SEZ,
  perifocal, LVLH and RSW) and geodesy (WGS84 geodetic coordinates,
  azimuth, elevation and range). Later: Lambert.

Two pieces of the language came out of trying this, in the same build:
`x to a to b` chains from the left, and `pointAt : Chart c -> Diff c ->
Point c` places a computed amount on a chart from its origin, in place of
`[0, 0, 0] c .+ withAxes c v`.

*As built* (the first build: the sets, `Body`, `kepler`, `maneuver`, the
two language additions; time, frames and geodesy are the second):

- **Nesting works with the namespace machinery as it is.** The seed's
  `astro` block holds nested `namespace` blocks (`Metron.Prelude`'s
  `Namespace` statement), so the sets are `astro.wgs84.earth` and so on,
  and the §7.7 checks cover them. An enclosing namespace is not searched
  (§7.6), so the inner blocks say `use astro` to read a body's fields, and
  a user does too: `earth.mu` needs `:use astro` (fields resolve through
  the scope only), while `period earth (7000 km)` needs only `:use
  astro.kepler` and a set. Two sets used at once make `earth` ambiguous,
  as designed. `:ls` counts a nested block's labels in its top namespace,
  `namespace astro (91 names)`, and `:ls astro` lists them by their path
  under it, `wgs84.earth : Body`.
- **The constants**, each cited beside it in `Metron.Prelude`. A
  defining constant is exact; a measured one carries its published
  uncertainty with `±σ`, read as a standard uncertainty where the source
  does not say; a field a source does not define is an exact zero.

  | set | body | value | source |
  |---|---|---|---|
  | `astro` | `G` | `6.67430e-11 ±σ 1.5e-15 m³ kg⁻¹ s⁻²` | CODATA 2018 = 2022 (NIST) |
  | `wgs84` | `earth.mu` | `3986004.418e8 m³/s²`, exact (defining; eq. 3-3 quotes 1σ `0.008e8`) | NIMA TR8350.2 3rd ed., eq. 3-3, Table 3.1 |
  | | `earth.radius` | `6378137 m` | TR8350.2 eq. 3-1, Table 3.1 |
  | | `earth.flattening` | `1 / 298.257223563` | TR8350.2 eq. 3-2, Table 3.1 |
  | | `earth.j2` | `−√5 C̄20`, `C̄20 = −0.484165371736e-3 ±σ 0.35610635e-10` (tide-free, 1986.0) | EGM96, NASA/TP-1998-206861 App. C; TR8350.2 eq. 7-1, Table 5.1 |
  | | `earth.rate` | `7292115e-11 rad/s` | TR8350.2 eq. 3-6, Table 3.1 |
  | `iers2010` | `earth.mu` | `3.986004418e14 ±σ 8e5 m³/s²` (TCG) | IERS TN36 Table 1.1 |
  | | `earth.radius` | `6378136.6 ±σ 0.1 m` (zero tide) | TN36 Table 1.1 |
  | | `earth.flattening` | `1 / (298.25642 ±σ 0.00001)` (zero tide) | TN36 Table 1.1 |
  | | `earth.j2` | `1.0826359e-3 ±σ 1e-10` (zero tide) | TN36 Table 1.1 |
  | | `earth.rate` | `7.292115e-5 rad/s`, exact (Table 1.1 has none) | TN36 Table 1.2 (GRS80 nominal) |
  | | `moon.mu` | `(0.0123000371 ±σ 4e-10) × earth.mu`; other fields 0 | TN36 Table 1.1, the Moon-Earth mass ratio |
  | | `sun.mu` | `1.32712442099e20 ±σ 1e10 m³/s²` (TCB) | TN36 Table 1.1 |
  | | `sun.j2` | `2.0e-7`, exact (adopted for DE421); radius, flattening, rate 0 | TN36 Table 1.1 |
  | `iau2015` | `earth` | `mu = 3.986004e14 m³/s²`, `radius = 6.3781e6 m`, `flattening = (6.3781e6 − 6.3568e6) / 6.3781e6` (derived from R_e, R_p); j2, rate 0 | IAU 2015 Resolution B3 |
  | | `sun` | `mu = 1.3271244e20 m³/s²`, `radius = 6.957e8 m`; others 0 | Resolution B3 |
  | | `jupiter` | `mu = 1.2668653e17 m³/s²` (without the Galilean satellites), `radius = 7.1492e7 m`, `flattening = (7.1492e7 − 6.6854e7) / 7.1492e7`; j2, rate 0 | Resolution B3, Explanation 8 |
  | `de440` | `mu` (km³/s², TDB, exact: no σ published) | `sun 132712440041.279419`, `mercury 22031.868551`, `venus 324858.592`, `earth 398600.435507`, `moon 4902.800118`, `mars 42828.375816`, `jupiter 126712764.1`, `saturn 37940584.8418`, `uranus 5794556.4`, `neptune 6836527.10058`, `pluto 975.5` (Mars to Pluto: the systems) | Park et al. 2021, AJ 161:105, Table 2 |
  | | radius, j2 | `earth 6378.1366 km, 1.08262539e-3`; `moon 1738 km, 2.03214360135e-4`; `sun 696000 km, 0.219613915165298248e-6`; others 0; no flattening or rate | `header.440` (RE, J2E, AM, J2M, ASUN, J2SUN) |

- **The solvers** iterate Newton's method on midpoints (`mid`), from
  `M + e sin M` (elliptic) or `asinh (M / (e − 1))` (hyperbolic), ten
  steps, then take one step on the values themselves, so the result
  carries the inputs' uncertainty to first order, and add `±` the bound
  `|f(E)| / (1 − e)` (`/ (e − 1)` for the hyperbola), computed from the
  residual's enclosure and `e`'s, so it is exact. (Since the mark is
  re-judged, §3.2, the residual on the values is marked for a `±σ`
  input, its first order cancelling; `|f(E)|` is bounded by the residual
  at the midpoints and twice the residual's bound radius on the values,
  without its `mid`.) Iterating on midpoints
  keeps the intermediate iterates' nudges, which mean nothing, out of the
  result; `mid` refuses a value marked non-linear, so such an input is an
  error. The parabola is closed form (Barker, `B = c − 1/c`). Vallado
  Ex. 2-1 comes out `220.51207476752206740… deg` with a bound below `1e-22
  rad`.
- **`fromState`'s cases** are decided by comparison with zero: circular
  when the eccentricity vector is zero, equatorial when the node vector is.
  A value too uncertain to decide is an error ("cannot decide
  comparison"). So the circular cases are decided from exact states (and
  the equatorial ones from states whose node vector is exactly zero, as
  `toState` gives for `i = 0`, since `sin 0` is exact); a circular
  orbit's state from `toState` is an enclosure, its eccentricity vector
  zero only to within it, and `fromState` refuses it. Whether a
  tolerance should decide instead is the owner's call. The record keeps its shape in each case (`argp = 0` and
  `nu` the argument of latitude; `raan = 0` and `argp` the longitude of
  periapsis; both, and `nu` the true longitude). Angles are in [0, 2π),
  as Vallado gives them, through `fullAngle`, `π + atan2 (−y) (−x)` with
  an exact zero on the positive x axis; a hyperbola's anomalies are in
  (−π, π). `toState` writes the perifocal axes in sines and cosines, not
  through `euler313`, because `expm` refuses statistical inputs.
- **`maneuver`'s** burns are signed (after less before) and a `Transfer`
  has three, `dv3 = 0` for two-burn transfers: a namespace cannot have
  two records with a field of one name, so one record serves.
- **Limits found.** `atan2` near ±90° (its `x` small against `y`) marks a
  tiny σ hugely non-linear (`atan2 ((1 ±σ 0.001) m) ((0.03 ±σ 0.001) m)`
  is "second-order term 120000%"), so `fromState` of a state with `±σ`
  fails where an angle is near a right angle; with `±` it works. That is
  `Metron.Affine`'s, not the library's.

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
- Type abstractions and applications are erased except where a value's
  runtime shape or dimension comes from a type alone: the element type of an
  empty tensor literal, and the instantiated type of `vmap`, `vzipWith` and
  `timap`, which gives their result's dimension (§3.3). An abstraction over a
  length, shape or dimension variable that its body needs there, or passes
  on in a type application, waits for its argument, and each application
  supplies it, resolved under the arguments in force where it is written;
  closures capture those arguments. Every other abstraction evaluates its
  body once, shared by all its applications, so a polymorphic value is not
  recomputed per use. A variable that nothing applies, at the top of an
  expression or never used, is unconstrained, and the evaluator takes any
  instance of it (an empty shape, length zero, dimensionless); the prompt
  refuses a value whose type leaves one open (§3.3), so that never prints.
- `DictLam` is an ordinary lambda over a dictionary value; `DictApp` applies it.
  A monomorphic `PrimApp mul@Mat×Vec [a, b]` is a direct call with its arguments
  as thunks, forced as the primitive needs them. There is no dispatch on value
  tags and no arity bookkeeping in the evaluator; the type checker has already
  guaranteed the shapes and dimensions match, so the evaluator does no dimension
  checking beyond maintaining the vector for printing.
- Closures capture the environment. Application is call-by-need: Haskell's own
  laziness supplies thunks, which `case` and recursion rely on. As built
  (§8.1), so that a long run keeps only what it still needs: a closure keeps
  the variables its body uses and no others (a function term carries that
  set, computed once); an argument that is a variable is the thunk it is
  bound to, not a new one around the environment; a call in tail position
  is a Haskell tail call, so a loop runs in constant stack; a value's
  shape, dimension and display unit are evaluated with it; and a call
  evaluates first the arguments its function certainly evaluates
  (`Metron.Strictness`: a case evaluates its scrutinee and what every
  alternative evaluates, a strict primitive its operands, a saturated call
  of known signature the arguments it is strict in, a cycle's members
  solved together from all-strict down). Errors are values, not
  exceptions, so evaluating an argument early raises no error the program
  would not have raised; the components of a number, or of a tensor or point
  of at most 64 components, are evaluated with it, a larger tensor's stay lazy;
  a component the function never reads is then computed anyway, or, if it
  never finishes, stops at `steps`.
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

### 8.1 Resource limits (design; decided by the owner, 2026-11-01)

A program in Metron can ask for more than a machine has: a huge exact
number (`2^(2^64)`, `1e1000000000`), rationals that grow with every step of
an iteration, recursion with no base case, an enormous list (`range 0 1e9`),
a vast tensor. Each such program must fail as an ordinary error naming the
limit it hit, never by exhausting the machine. A limit is a run-time setting,
changed with `:set` (and on the command line), with a default that a normal
session never reaches.

| setting | what it bounds | where it is checked |
|---|---|---|
| `:set memory` | the heap, in GB (the GHC runtime's maximum heap) | the runtime: a heap overflow becomes the error "the expression needed more than N GB (`:set memory`)", the session survives |
| `:set steps` | evaluation steps per expression (fuel) | the evaluator, counted per reduction |
| `:set depth` | nesting of calls | the evaluator |
| `:set digits` | ~~the size of an exact integer or rational, in decimal digits~~ a number's magnitude, its decimal exponent either way (as built, by the owner's decision in §3.2.8: an exact result's length is the precision's) | arithmetic, *before* computing where the size can be predicted (a power's result from its exponent, a literal's exponent, an exponential), after otherwise |
| `:set components` | a tensor's ~~or a list's~~ elements (as built: a list's length is not known until it is walked, so `steps` and `memory` bound it) | construction (formerly the fixed `componentLimit`, 10⁷) |
| `:set time` | wall-clock seconds per ~~expression~~ input (as built: a line at the prompt, a `-f` file, a `:load`) | the REPL, by a timeout; off by default |

The defaults are chosen by measurement, so that the test suite, the library
and the tutorial run well inside them while a runaway stops within seconds:
a starting point is `memory` 4, `steps` 10⁹, `depth` 10⁵, `digits` 10⁵,
`components` 10⁷. `:set` with no arguments lists them. A limit is a
property of the session, not of a term: it never changes a value or a hash,
only whether an evaluation finishes. Precision (`:set precision`) is
separate, being a property of the result.

#### 8.1, as built (2026-11-01)

**The limits.** `Metron.Limits` holds them; `:set` lists them after the
other settings, `:set NAME VALUE` changes one, and `metron --set NAME
VALUE`, any number of times, starts a session with one changed. A value
is a positive whole number, written `100000000`, `100_000_000` or `1e8`;
`time` also takes `off`. Each limit, when hit, is an ordinary error that
ends with the setting to change, and the session goes on:

| setting | default | how it is checked | the error |
|---|---|---|---|
| `memory` | 4 GB | the runtime's maximum heap, set at startup and whenever the setting changes: `RtsFlags.GcFlags.maxHeapSize`, which the collector reads at every collection, so a change takes effect at once (measured: `:set memory 1` stops `reverse (range 0 1e8)` at 1.1 GB). The executable links with `-rtsopts`; `--set memory` supersedes `+RTS -M`. The runtime throws `HeapOverflow` to the main thread, which in the executable is the one evaluating; it is caught around each input, whose outputs are forced inside the handler, and a collection frees what the input built | `the evaluation needed more than 4 GB` |
| `steps` | 10⁸ per expression | every reduction of the evaluator counts against a budget made for that expression's evaluation | `the evaluation took more than 100000000 steps` |
| `depth` | 10⁵ | the budget's second counter: one level for each value something waits for (an operand, a scrutinee, the function of a call, a thunk when forced); a call in tail position is no deeper | `the evaluation nested more than 100000 calls deep` |
| `digits` | 10⁵ | a number's magnitude, `log₁₀` of its size from the leading bits of its numerator and denominator. Before computing: a power from its exponent (`n · log₁₀ |x|`), a literal in the lexer from its exponent, an exponential (`exp`, `sinh`, `cosh`) from its argument. After: every result of `+ − * /`, `outer` and `dot` | `the power would have more than 100000 digits`, or `… zeros after the point` |
| `components` | 10⁷ | where a tensor is built: `noise`/`gauss`, a stack of tensors, `outer`, `dot`, a matrix from a vector. A length a type or a literal names has a fixed bound of 2^40 instead, so that a definition checks the same in every session | `the result would have 16000000 components, more than 10000000` |
| `time` | off | `System.Timeout` around each input | `the input took more than 2 seconds` |

The budget is counted in place: the evaluator is pure, its values lazy
thunks, and threading a counter through them would make every value a
computation. `newBudget` makes a pair of counters per evaluation (in
`Compile.runtimeWith`); `spend` and `nested` read and write them with
`unsafeDupablePerformIO`, `NOINLINE` and an argument that makes each call
its own. A limit reached is a `Left`, an `EvalError` like any other, so
`feed` stays pure and the tests see it; `memory` and `time` are the only
ones that need `IO`, in `runLimited`. A Haskell stack overflow is caught
there too and named `depth`, but the stack is heap, so `memory` stops it
first.

**Leaks fixed rather than limited.** Measuring the catalogue below found
that most of the runaways were not programs asking for much but the
evaluator keeping what it no longer needed:

1. *No tail calls.* An application checked, after the call, whether it
   had made a moving chart's instant, so every call held a Haskell frame:
   `let loop n = loop n` grew the stack without end. The check is now made
   first, from the term, and the call is the last thing done.
2. *A variable passed on became a new thunk around the whole environment*,
   so `loop n = loop n` chained every environment it went through. A
   variable is now its own thunk (`delay`), and a literal is built at once.
3. *A value's dimension and display unit were thunks over its
   operands'*, so `n - 1` in a loop kept every earlier `n` (`hh 1000000`,
   a counting loop, held 870 MB). `VTensor`'s and `VPoint`'s shape,
   dimension and display unit are strict fields; a magnitude's rationals
   are strict too.
4. *A closure kept its whole environment*, so the lambda in `length xs =
   foldl (\n _ -> n + 1) 0 xs` kept the list's head for the whole fold. A
   function term (`TLam`, now a pattern over `TLamWith`) carries the set
   of variables free in its body, computed once and shared, and a closure
   keeps only those, the choice made when the closure is built (a lazy
   choice kept the variable anyway).
5. *A lazy accumulator*: `go n acc = if n == 0 then acc else go (n - 1)
   (acc + 1)` built one thunk per step, and `f n = f (n + 1)` grew until
   the machine ran out. `Metron.Strictness` (§8) finds the arguments a
   call certainly evaluates and the evaluator evaluates them first, with a
   number's or a small tensor's components; both loops now run in constant memory, `f 0` until
   `steps` stops it.
6. *`std.foldl` is lazy by definition*, so `length`, written with it, kept
   a million-deep chain of `n + 1`. `std.foldl'` and the primitive `seq`
   are new (§7.7), and `length` and `reverse` use `foldl'`.
7. *Sums were quadratic*: each `addM` filtered every coefficient for
   zeros, and compaction sorted by insertion. Only coefficients two forms
   share can cancel, so only those are checked; compaction sorts in
   `n log n`. The results are the same.

The catalogue, each program measured alone with peak RSS under a 6 GB
cap and a 60 s timeout, before (main at `d89f2a4`) and after (time, peak
RSS, outcome); the numbers in the cause column are the fixes above:

| program | before | after | cause |
|---|---|---|---|
| `1e1000000000` | 60 s timeout, 4.0 GB | 0.07 s, 32 MB: refused, `digits` | the lexer wrote out `10^e` |
| `2^18446744073709551616` | 60 s timeout, 5.3 GB | 0.08 s: refused, `digits` | the power was computed exactly |
| `exp 1000000`, `exp (-1000000)`, `sinh 1000000` | 16 s, 89 s, past 120 s | 0.07 s each: refused, `digits` | the series was summed at the result's size |
| `let f n = f (n + 1)`, `f 0` | killed at 6 GB, 4.6 s | 5.5 s, 32 MB: `steps` | 1, 2, 5 |
| `let loop n = loop n`, `loop 0` | killed at 6 GB, 4.7 s | 2.4 s, 32 MB: `steps` | 1, 2 |
| `hh 1000000`, a countdown in tail position | 1.2 s, 870 MB | 0.56 s, 32 MB | 1, 3 |
| `go 1000000 0`, a counting accumulator | 2.3 s, 1.9 GB | 0.8 s, 32 MB | 5 |
| the same with a 6-vector, and with `1 m` | 1.6 s, 778 MB (300000 steps); 1.6 s, 690 MB (this branch, before the last fix) | 1.2 s and 1.1 s, 32 MB | 5, for a tensor of up to 64 components; a sum's unit was a choice left in a thunk |
| `g 1000000`, `1 + g (n - 1)` | 1.9 s, 1.5 GB: finishes | 0.15 s, 49 MB: `depth` | real nesting; `:set depth 2e6` finishes in 1.4 s, 467 MB |
| `fact 100000` | 2.7 s, 173 MB: finishes | 0.18 s: `depth`; with depth raised, `digits` (456574 digits) | real nesting and a real size |
| `fst (Pair 1 (range 0 1e9))` | 0.07 s, 32 MB | the same | a lazy list is fine |
| `length (range 0 1e6)` | 3.7 s, 3.3 GB | 1.3 s, 32 MB | 4, 6 |
| `length (range 0 1e8)` | killed at 6 GB, 5.6 s | 4.3 s, 32 MB: `steps` | 4, 6; ten million elements need `:set steps 1e9` |
| `foldl (\n x -> n + x) 0 (range 0 1e6)` | 3.8 s, 3.3 GB | 2.1 s, 1.4 GB: `depth` | lazy by definition: forcing the result walks a million-deep chain; `foldl'` runs in 32 MB |
| `reverse (range 0 1e8)` | killed at 6 GB, 5.6 s | 11 s, 3.9 GB: `steps` | the list is kept whole by design; `memory` is next |
| `iter (1/3) 20`, exact logistic map | 12.9 s, 39 MB | 12.9 s, 40 MB | rationals that double their digits; since exact while small (§3.2.8, as built), 0.10 s, 19 MB |
| `norm (noise 1000000)` | 60 s timeout, 0.49 GB | 6.8 s, 1.7 GB | 7 |
| `norm (gauss 1000000)` | 3.4 s, 1.8 GB | 3.1 s, 1.5 GB | a million statistical nudges, about 1.5 KB each, are real |
| `noise 9000000` | killed at 6 GB, 27 s | 24 s, 4.3 GB: `memory` | within `components`; nine million nudges are real |
| `(outer (noise 3000) (noise 3000)).0.0` | 0.7 s, 0.67 GB | 0.9 s, 0.80 GB | nine million lazy components, each now checked for `digits` |
| `(outer (noise 4000) (noise 4000)).0.0` | refused, fixed limit | 0.07 s: refused, `components` | |
| `2^100000`, `exp 200`, printed | 0.09 s, 32 MB | the same | printing a long exact value is cheap |
| `log 1e-99999` | 33 s, 0.96 GB | 28 s, 0.97 GB | its series in exact rationals; since its series run in fixed point (§3.2.8, as built), 0.10 s, 19 MB |
| a cycle's member referenced from outside it, `ev 2` 300000 times in a loop | not measured | 0.81 s, 32 MB (0.46 s for a function that is no cycle's) | a reference re-ties the cycle each time: a constant cost, not a leak |

The test suite, run with every QuickCheck property at 2000 cases under a
3 GB cap, is green in 29 s with a peak of 1.0 GB, the generator's slowest
property taking 2.3 s for its 2000 cases.

**The defaults, and why.** Measured with every limit lowered until
something failed: the whole test suite (700 tests, the astro solvers'
Newton iterations among them) needs fewer than 3·10⁵ steps and 300 levels
of nesting in any one expression, the tutorial's examples fewer than
3·10⁴ and 50, and the largest magnitudes the suite writes are beyond
`10^±60`. The evaluator takes about 18 million steps a second, so `steps`
at 10⁸ stops a runaway in about 5 s with room for 300 times the suite's
largest expression; the design's starting point, 10⁹, took 54 s to stop `f
0`. The cost is that a fold over ten million list elements needs `:set
steps 1e9`. `depth` at 10⁵ is about 50 MB of stack and stops a runaway
recursion in 0.15 s. `digits` at 10⁵ is the design's: far past any
physical quantity, and below what makes arithmetic slow. `components`
stays at 10⁷: the suite builds a 3000 × 3000 outer product, which needs
0.8 GB of lazy elements, so a tensor at the limit fits the 4 GB heap.
`memory` at 4 GB is the design's, about four times the suite's peak.

**What the limits do not stop.**

- *Exact rationals that grow without growing in size* ~~only `:set time`
  stops~~: as built, an exact result past a size tied to the precision is
  rounded (§3.2.8, exact while small, as built). `iter (1/3) 20`, the
  exact logistic map, took 13 s and takes 0.10 s; `log 1e-99999` took
  28 s and 0.97 GB and takes 0.10 s and 19 MB, its series in fixed point
  and its operand's encoding linear. ~~What remains is a *linear* loop on a
  value that is already an enclosure, `x + 1/k` collecting the
  denominators of its exact terms (§3.2.8, as built, left open): `H₃₀₀₀₀`
  takes 13 s.~~ A linear loop on an enclosure is held to the same length
  (§3.2.8, linear results held, as built): `H₃₀₀₀₀` takes 0.20 s, and a
  series of exact terms `Σ xᵏ/k` to 30000 terms 0.80 s, where it ran past
  300 s. What remains is an exact value's *size*: `Σ xᵏ/k!` with exact
  terms pays each step for the `k log k` digits of `k!`, which `digits`
  bounds.
- *A chaotic iteration's enclosure grows until it is useless*: the
  logistic map at working precision is meaningful for about 100 steps at
  precision 20, then its enclosure covers more than `[0, 1]`, its square
  diverges, and `digits` stops it. That is the rigorous answer.
- *Many independent nudges*: each costs about 2 KB, so `norm (gauss
  1000000)` holds 1.5 GB, and `noise 9000000` reaches the 4 GB heap only
  after about 24 s of collections near the limit.
- *A list's length*: `components` counts tensors only; `steps` and
  `memory` bound a list.

**Where the build differs from the plan above**, besides the struck-out
words in the table: `steps` defaults to 10⁸, not 10⁹ (above); `time` is
per input, and an input that is a file is one; `digits` bounds magnitude;
`components` does not count a list; a literal is checked against the
session's `digits` at the prompt, in files and in `:type`, `:exact` and
the other commands that evaluate, but `:edit` and `:prefer` parse with the
default; and `--set memory` supersedes `+RTS -M`. The test suite measures
memory on its main thread before the tests start (`Limits.measure`), since
the runtime throws a heap overflow to the main thread and tasty runs a
test on another.

### 8.2 Backends (design; decided by the owner, 2026-11-01)

One Typed Core, several evaluators of its scalars. A **backend** is the
scalar arithmetic and the built-ins that belong to it; everything else is
shared: tensors, units and dimensions (checked statically anyway), charts,
data types, the store and hashes. A stored definition names no backend, and
the same term runs under any backend that has the built-ins it uses.

- **`:backend affine`** (the default) is the evaluator of §3.2: rationals
  with affine error forms, rigorous bounds and σ. Its own built-ins are the
  ones that read or make uncertainty: `±`, `±σ`, `noise`, `gauss`, `mid`,
  `sd`, `bound`, and the commands `:budget`, `:covariance` and `:exact`.
- **`:backend double`** evaluates scalars in Haskell `Double`, in the
  operation order of the formula as it would be written in Haskell, so a
  result here is the result a ported formula gives. A literal is parsed as
  an exact rational, as always, and rounded to the nearest double at the
  boundary. It follows IEEE 754 (decided by the owner, since the point is
  to run as Haskell does): `1/0` is `Infinity`, `sqrt (-1)` is `NaN`, and
  overflow is infinite, not an error. Printing says where the first NaN or
  infinity appeared. It carries a running error bound (Wilkinson and
  Higham's running error analysis: one extra double per value, bounding
  the accumulated rounding under the standard model of floating point,
  with a per-function figure for `sin`, `exp` and the other library
  functions, which are not correctly rounded). `precision` does not apply.
- **How `double` estimates its error: `:set samples N`** (decided by the
  owner). The arithmetic is the same under every setting: each scalar
  carries its ordinary round-to-nearest IEEE result, which is the value
  shown and the value a ported formula computes, and which alone decides
  every `if` and comparison, so a run takes the branches Haskell would.
  What else is carried is the setting's choice:
  - `samples 0` (the default) carries the running error bound above:
    guaranteed under the model, pessimistic, about twice the cost.
  - `samples N`, for `N > 0`, carries N copies computed in lockstep with
    random rounding, each operation rounding each copy up or down to a
    neighbouring double with equal probability: stochastic arithmetic, the
    CESTAC method behind CADNA (N = 3 is its usual choice). Their spread,
    scaled by Student's t, estimates the significant digits that survive:
    realistic, since rounding errors partly cancel as they do in practice,
    statistical rather than guaranteed, about N times the cost in one pass.
    When the copies disagree about a comparison that decides an `if`, the
    branch is flagged as numerically unstable ("`if disc > 0` goes both
    ways: the condition is lost in rounding"). The random choices come from
    a generator seeded by `:set seed` (a fixed default), so the same input
    under the same settings gives the same estimate.
- **Declared σ is sampled: Monte Carlo under `double`** (decided by the
  owner, 2026-11-01). Under `samples N > 0`, a declared standard
  uncertainty is no longer refused: each copy draws it. `x ±σ s` is `x +
  s·z` in each copy, `z` a standard normal, and `gauss` is drawn likewise
  (`noise`, which makes a bound unknown, is refused, below). The draw is keyed by the nudge's identity (§3.2.4), the
  copy and `:set seed`, so the same unknown has the same draw wherever it
  appears in a copy, and `x - x` is exactly 0 in every copy: the
  correlation affine forms keep by name, kept by the key. The shown value
  is still the IEEE result at the nominal inputs, what a ported formula
  computes; the copies measure the spread. This is the GUM's Supplement 1
  method, and it is the answer for a value `affine` marks non-linear: the
  copies give a skewed sample's real spread instead of a refusal.
  - `:set rounding nearest | random` (default `random`). With `random`
    each copy also rounds randomly (CESTAC), so the spread is input
    uncertainty and rounding together, the realistic total for a ported
    formula; with `nearest` the copies differ only in their draws, pure
    Monte Carlo, the fair comparison with `affine`'s σ. Under `samples 0`
    the setting has no effect.
  - `mid` and `sd` are the copies' mean and standard deviation under
    `double` with `samples N > 0`, and refused under `samples 0`, where no
    copies exist. They join `errorOf` and `digitsOf` as `double`'s; the
    check before running then depends on the setting for these two only.
  - Monte Carlo needs many copies, so `samples` goes up to 10⁵ (CESTAC's 3
    remains enough for rounding alone). The copies are computed in
    lockstep as before.
  - A bound `±` has no distribution, and sampling it uniformly would be an
    assumption the language never makes elsewhere, so `±` stays refused
    under `double`. A computation that mixes `±` and `±σ` runs under
    `affine`.
  - **The copies run in parallel batches** (decided by the owner,
    2026-11-01), for `double` with `samples N > 0` only. With `:set cores
    K` (default: the logical core count), the expression is evaluated K times
    in parallel, each evaluation carrying its batch of about N/K copies in
    lockstep; parallelising each operation across copies would cost a
    synchronisation per operation, too fine at about 0.1 µs a copy. Since a
    copy's draws and roundings are keyed by its global copy number, not by
    evaluation order, a result is identical for every K. The nominal IEEE
    value is computed once. Batches combine exactly: means and variances
    by the parallel update (Chan et al.), samples concatenated for
    quantiles, unstable-branch flags by union. The `steps` limit counts all
    batches together; the `memory` limit is the process's and covers them.
    `affine` and `samples 0` are unaffected.
  - **Corrections after building** (decided by the owner, 2026-11-01):
    - *Printing under Monte Carlo.* When a value's copies carry draws of
      declared σ, it prints its nominal IEEE value with the sample beside
      it, `0 (Monte Carlo: mean 1.015, sd 1.441, 10000 samples)`, not `±`
      the standard error of the copies' mean, which described only rounding
      and made `n*n` look pinned at 0. `errorOf` and `digitsOf` measure
      rounding, so they refuse a value whose copies carry draws ("its copies
      carry declared σ; read `sd`"); with rounding alone they are as before.
    - *`noise` is refused under `double`.* It makes a bound unknown (`x ±
      e` is `x + e * noise 1`), so drawing it as a normal would let a bound
      in as a σ. `gauss` is drawn; `noise` is refused as `±` is.
    - *`steps` applies to each batch,* as to one evaluation: every batch
      takes the same steps, so an input is accepted or refused alike for
      every `K`. This replaces "counts all batches together".
    - *The default for `cores` is the logical core count,* since the
      runtime does not expose physical cores.

    *As built (2026-11-01): the corrections.* A number's copies say what
    they spread by, `Metron.Double.Spread`: rounding alone, or draws as
    well. A draw of a declared unknown carries draws; a literal's and
    `pi`'s copies do not; an operation's result carries them when any
    operand's do (`x + (0.1 + 0.2)` does, `0.1 + 0.2` does not), so `x -
    x` still carries them, all zero, and prints `0 (Monte Carlo: mean 0,
    sd 0, 10000 samples)`; `mid` and `sd` are numbers known exactly and
    carry none; merged batches keep the flag. A value any of whose numbers
    carry draws prints its IEEE values alone, then each number's mean and
    deviation laid out in the value's own shape and unit: `5828.501263698674
    s (Monte Carlo: mean 5828.5079 s, sd 0.3027 s, 10000 samples)` for the
    orbital period below, `[0, 0, 2] m (Monte Carlo: mean [-0.016, 1.015,
    2] m, sd [1.0073, 1.441, 0] m, 10000 samples)` for `[n, n * n, 2] * 1
    m`. A record or a tuple prints each field so. The digits (chosen
    here): each statistic is rounded to the place of the second
    significant digit of its own standard error, `s/√N` for the mean and
    `s/√(2(N − 1))` for the deviation, trailing zeros kept, as the
    shortest digits when that error is 0 or the place asks for more digits
    than a double holds. That gives example one's `1.015` and `1.441`
    exactly; the second example's `5828.50` and `0.065` are not the
    standard error's digits at 10⁴ samples, so it was taken for the form
    only. `errorOf` and `digitsOf` refuse a number that carries draws,
    "`` `errorOf` measures rounding: its copies carry declared σ; read
    `sd` ``", at run time, since the check before running cannot see
    draws. `noise` left `sampledOwn`, so the check refuses it at every
    setting with "`` `noise` is the affine backend's; the double backend
    does not have it ``", and the backend refuses it too. The `steps`
    budget lost its share: each batch counts its own steps against the
    whole limit. `cores` needed no change: the command line takes
    `getNumProcessors`, the logical count, which `:set` lists as `cores
    K`. Building it found the copies' mean taken by a plain sum, which
    rounds in its last digits over 10⁴ copies and so gave copies that
    agree a spread of their own (`errorOf (0.1 + 0.2)` at 10⁴ copies
    rounded to nearest was `7.0e-16`); the mean is now taken about the
    first copy, `c₀ + Σ(cᵢ − c₀)/N`, and that is `0`.

  *As built (2026-11-01): Monte Carlo.* `Metron.Double`'s `noiseM` and
  `uncertainM`. A unit unknown is a number whose value is 0 and whose
  copies are standard normal draws; `x ±σ e` is then `x + |e|·z` by the
  backend's own `+` and `*`, so the shown value is `x`'s IEEE value, the
  sum and the product round as the copies do (`:set rounding`), and the
  `v ±σ P` form, which goes through `gauss` and Cholesky, gets correlated
  draws for nothing. `|e|` as affine sizes the nudge, so a label reused
  with a negative `e` is not anti-correlated.
  - *The key* of an unknown is the first eight bytes of the SHA-256 that
    names the same nudge under `affine` (`Affine.originId`: kind, owner
    stamp, path, component, and the midpoint, here `x`'s IEEE value; the
    label alone for `#label`), one hash per declared component.
  - *The generator* (chosen here): Box–Muller on two uniforms. From the
    key, the seed and the copy number, SplitMix's finaliser gives a base
    word, then two words by finalising `base + 1` and `base + 2`; each
    gives a uniform `u = (⌊w / 2¹¹⌋ + 1)·2⁻⁵³` in `(0, 1]`, so `log u₁` is
    finite; `z = √(−2 ln u₁)·cos(2π u₂)`. Only the cosine of the pair is
    used, so a draw depends on its key, seed and copy and on nothing else:
    not on order, not on how many other unknowns there are. The largest
    `|z|` it can give is `√(2·53 ln 2) ≈ 8.6`, a tail cut far beyond
    anything 10⁵ samples resolve. Checked: `gauss 2` at 10⁴ copies has
    mean, deviation and correlation within five standard errors of 0, 1
    and 0.
  - *`mid` and `sd`* are the copies' mean and their deviation with `N −
    1`, each a number known exactly. A number with no copies under samples
    (an exact constant such as `errorOf x`) has its value as its mean and
    0 as its deviation.
  - *The check* depends on `:set samples` for `±σ` and `gauss` as well as
    `mid` and `sd`: the two forms must pass it under `N > 0` too, so
    "these two only" above is loose. `Metron.Scalar.refusalOf`
    answers per backend, samples and name: available, lacked, or needing
    samples; the memo still holds names only. Under `samples 0`: "`` `sd`
    needs `:set samples N` under the double backend ``", or, through
    definitions, "`` `orbitError` uses `sd` (through `budgetOf`), which
    needs `:set samples N` under the double backend ``". `±`, `noise`,
    `bound`, `covariance` and `crossCovariance` are refused under every
    setting.
  - *Checked against `affine`.* The orbital period `2π√(a³/(G·M))` with
    CODATA's `astro.G` and `M = 5.9722e24 kg ±σ 6e20 kg` at 10⁴ copies,
    rounding to nearest: `sd` 0.30270 s against affine's first-order
    0.30002 s (0.9 %, within five standard errors of a normal sample's
    deviation, `5/√(2(N − 1))` ≈ 3.5 %); the same for a product of two
    small-σ values. `n * n` for `n = 0 ±σ 1`, which affine marks
    non-linear and refuses `sd` of: mean 1.015 and deviation 1.441, within
    five standard errors (`√2/√N` for the mean; `√(56/N)/(2√2)` for the
    deviation, n²'s fourth central moment being 60).
  - *Cost.* The copies stay one unboxed vector per number, computed in
    lockstep. The orbital period above with its `mid` and `sd`, a seeded
    session started each time, single core, rounding at random: 0.07 s
    and 33 MB at 10³ copies, 0.11 s and 34 MB at 10⁴, 0.40 s and 58 MB at
    10⁵. A heavier workload, 100 positions each from ten Newton steps of
    Kepler's equation, at 10⁴ copies: 16 s, 38 MB, about 25 ns a copy per
    operation.
  - *Closed by the corrections above.* `noise` was drawn as a standard
    normal, so `x + e * noise 1` ran where `x ± e` was refused; it is now
    refused as `±` is. The printed `± e`, `errorOf` and `digitsOf` were
    CESTAC's `τ·s/√N`, the error of the copies' mean, not the spread of
    the input (`1 ±σ 0.1` printed `1 ± 0.0020 (estimate, 10000
    samples)`); it now prints `1 (Monte Carlo: mean 1.0001, sd 0.10034,
    10000 samples)`, and `errorOf` and `digitsOf` refuse it.

  *As built (2026-11-01): parallel batches.* `Metron.Batch` and
  `Compile.batchedValue`. `:set cores K` and `--set cores K`; the command
  line starts it at the machine's logical cores (`getNumProcessors`),
  which `:set` lists as `cores K`, raising the runtime's
  capabilities to them unless `+RTS -N` chose; a library session starts
  at 1. Each batch is a whole evaluation in its own thread (`async`'s
  `forConcurrently`, now a dependency) with its own runtime and budget;
  `Settings.batch` names its copies, and the coins of `operation`, the
  copies of a literal and of `pi`, and the draws all take a copy's
  global number.
  - *Combining.* The batches' copies are concatenated in order, and the
    statistics computed from the whole vector as before, so the result
    is the single evaluation's bit for bit at every K. The tests check
    copies and statistics at K = 1, 2 and 4 against the unbatched
    evaluation, but the test suite is not threaded, so its batches run in
    turn; with real threads, only the executable's printed output (two
    digits of each estimate) was compared, at K = 1 and 32 on the orbit
    workload below. Chan's parallel update, which the bullet names, sums
    in an order that depends on K, so it would not be bit for bit. The
    IEEE value is computed in every batch, alike, and taken from the
    first. Each batch forces its value as the printer does, in order and
    up to the first error, so it makes the reductions one evaluation's
    printing makes and no others. A warning records the step it was made
    at, the same in every batch, and the batches' warnings print in the
    order of the first step any made each at, which is one evaluation's
    order; they say the total N.
  - *One evaluation instead* when the input reaches `mid`, `sd`,
    `errorOf` or `digitsOf` (they read across a number's copies and
    would see only their batch's; the check's memo says which an input
    reaches), when the value holds a chart, and when the batches
    disagree in anything but their copies. So `sd T` does not run in
    parallel; `T` does. K is at most N/2, so a batch always has the two
    copies a spread needs.
  - *Steps.* Every batch takes the same steps, since the same IEEE
    values decide every branch, and each counts its own against the
    whole limit, as one evaluation does (corrections above), so an input
    is accepted or refused alike at every K: `go 1000 0`, between 5000
    and 20000 steps, runs under `steps 20000` at K = 1 and at K = 4. A
    batch that reaches the limit fails the input with the user's limit
    named. (Until the corrections, a batch stopped once K times its own
    count passed the limit, which refused that input at K = 4.) *Open:*
    `exactly`, which asks whether a number's copies
    spread at all (an index position must be exact), sees only its
    batch's; a small batch can agree by chance where all N would not, so
    an index could be accepted batched and refused at K = 1. Rare, and
    not seen.
  - *The limits under threads.* A timeout or a heap overflow reaches the
    waiting thread, and `forConcurrently` stops the batches. While they
    stop they go on allocating, and the runtime throws a second heap
    overflow, which reached the top level and ended the session in two
    runs of six at 32 batches. `runLimited` now runs masked and takes in
    any further overflow after the first: ten runs in ten report `:set
    memory` and go on to the next input.
  - *The runtime.* With 32 capabilities, GHC's parallel collector slowed
    affine: `f 0` to the `steps` limit took 7.6 s and the million-step
    loop 1.1 s. The executable now runs the young generation's
    collections on one thread and the older generations' on four
    (`-with-rtsopts=-qg1 -qn4`): 6.1 s and 0.87 s, as with a sequential
    collector. `samples 0` is unchanged (it never batches).
  - *Speed-up* on the orbit workload (100 positions, each from ten Newton
    steps of Kepler's equation, `a = 7000 ±σ 1 km`) at 10⁴ copies, on an
    i9-14900K (8 performance and 16 efficiency cores, 32 threads): K = 1
    7.9 s, K = 2 4.3 s, K = 4 2.4 s, K = 8 1.7 s, K = 16 1.6 s, and the
    default 32 2.0 s, 4.0 times faster; past 8 the efficiency cores and
    the shared cache cap it, and K = 16 beats the default on this
    machine. At 10⁵ copies, default K: 18 s and 250 MB.
    The orbital period, at most 0.3 s at any N, is dominated by starting
    the session.
- **`double`'s built-ins are the same under every setting,** so the
  before-running check depends only on `:backend`. `errorOf x` is the
  absolute error estimate (the bound under `samples 0`, the scaled spread
  under `samples N`) and `digitsOf x` the significant digits it implies; a
  check such as `digitsOf r < 10` is written once and run either way.
  Printing says which kind of estimate a value has, `3.3e-16 (bound)` or
  `4.1e-17 (estimate, 3 samples)`. The rest describe the format and do not
  depend on the setting: `ulps`, `eps`, `nextUp`, `fma`, `isNaN`,
  `isInfinite`. `samples`, like `precision`, is a session setting: it
  changes what a stored function computes, never its hash. A built-in that
  returns the raw copies (`samplesOf`) is left out until there is a use for
  it.
- **The command:** `:backend` names the current backend, `:backend
  double` switches, and `--backend double` chooses one on the command
  line, as `--set` does.
- **Built-ins a backend lacks are refused before running.** When a
  definition is entered, the walk of its Core that already finds its
  dependencies also collects the backend-specific primitives it calls
  directly. What a definition needs is its own set and its dependencies':
  `needs(h) = direct(h) ∪ ⋃ needs(d)`, one union for a recursive group.
  A hash names an immutable term, so `needs(h)` is memoised by hash forever
  and never invalidated: `:update` makes new hashes. An input's check walks
  its own Core and looks up `needs` of the hashes it refers to, so the
  library is never walked again. The cache holds primitive names, not
  backends, so a new backend, or a primitive added to one, changes nothing
  cached. On failure only, a search of the dependency graph finds the path
  for the message: "`orbitError` uses `sd` (through `budgetOf`), which the
  double backend does not have". The check is sound, since every function
  value, closure and record is built from Core in the closure, and
  conservative, as a type check is: `if false then sd x else 0` is refused
  under `double`.
- **Building it.** First the evaluator becomes generic over its scalar
  domain, a refactor with no visible change, after the precision audit
  (§3.2.8), which changes the same code. Then the `double` backend and the
  check.
- **Open: `:trace`.** The porting tool would run an expression under
  `double`, shadowed by `affine` (the method of Herbgrind), and report each
  operation's local error in ulps and its amplification, naming the few
  operations, by source span, that lose the most. How the shadow follows a
  `double` run that has gone to `NaN` or infinity, or taken the other
  branch of an `if` that the exact value would not take, is undecided.

#### 8.2, as built (2026-11-01)

**The generic evaluator.** `Metron.Scalar` holds the class a backend
implements, `Scalar s`: its arithmetic, with the names and shapes of the
`Metron.Affine` functions and a `Settings` (working precision, comparison
policy, samples, seed) where those take the precision; its linear-algebra
kernels (`determinantM`, `invertM`, `matrixExpM`, `choleskyM`); the few
facts the shared code asks of a number (`literal`, `exactly` for index
positions and a route's zero offsets, `sizeOf` for the `digits` limit,
`stepProblem` for a chart's step, `hintFactor` for a display unit);
`noiseM` and `uncertainM` for the uncertainty forms of Core; and `own`, a
table of the backend's own built-ins by name, each described by its
shape (componentwise, a covariance, a test, a constant, numbers to a
number), so the evaluator supplies the tensors, dimensions and display
units. A class and not a record of functions: the scalar type determines
the backend, so a value of one can never meet an operation of the other,
and the evaluator, the printer and the tests name a backend by a type.

Values, charts, closures and runtimes take the scalar as a parameter
(`ValueOf s`, `ChartOf s`, `RuntimeOf s`); `Value`, `Chart`, `Thunk` and
`Runtime` are the affine backend's, so the code and the tests that only
know affine are unchanged. Tensors, units and hints (whose factors stay
exact magnitudes), dimensions, charts, data, closures, limits and the
shape of printing are shared; the printer's numbers go through a small
`Display` class in `Metron.Pretty`. `mid`, `bound`, `sd`, `covariance`
and `crossCovariance` moved from the shared primitives into the affine
table. The evaluator is specialised for each backend (`SPECIALIZE`),
which keeps the hot path as fast as before: `f 0` to the `steps` limit
takes 5.9 s, as on main, and a million-step counting loop 0.84 s.

**The double backend** (`Metron.Double`). A number is its IEEE result,
its estimate (a bound, or the copies) and, once it is not finite, where
the first NaN or infinity came from (the operation and its operands, `1 /
0`, `sqrt (-2)`: Typed Core has no source spans to name). Every operation
is GHC's `Double` operation on the values, so the results equal GHC's for
the same formula in the same order (tested over 33 expressions); `x ^ n`
makes the multiplications of base's `^` (repeated squaring) and a
negative power is the reciprocal, as `^^`. GHC's rewrite rules for a
literal `x ^ 4` or `x ^ 5`, which multiply in a row, fire only in
optimised Haskell, so a ported literal power can differ in its last bit.
`floor`, `ceil` and `round` are Haskell's (`round` to even), on a finite
value; the rest of IEEE is as the design says.

*The running bound* (`samples 0`) bounds the distance from the result to
the exact value of the same formula on the exact literals:

- a literal's bound is its rounding, `|d − r|`, exactly, rounded up;
- `x ± y` adds the bounds; `x · y` adds `|x|e_y + |y|e_x + e_x e_y`; `x / y`
  adds `(e_x|y| + |x|e_y) / (|y|(|y| − e_y))`, unbounded when `|y| ≤ e_y`;
- each then adds its own rounding, `u·|z| + 2⁻¹⁰⁷⁴` with `u = 2⁻⁵³`,
  unless an error-free transformation (TwoSum; a fused multiply-add for a
  product or a quotient) proves the result exact, which a product or a
  quotient may only above the subnormals; so `0.5 * 4` stays exact;
- a library function propagates its operand's interval: a monotone one
  (`exp`, `log`, `sqrt`, `sinh`, `tanh`, `atan`, `asin`, `acos`, and `tan`
  between poles) by the larger change at the interval's ends, each end's
  own library error included; `cosh` the same with its minimum at 0; `sin`
  and `cos` by `|h|·|f′(x)| + h²/2`, at most 2; `atan2` by `(e_x +
  e_y)/r_min`, at most 2π, and 2π across the branch cut. An interval that
  leaves the domain, or reaches a pole, is unbounded;
- a library function then adds its own error, in units in the last place
  of its result (`ulp(z) ≤ 2u|z|`), a figure chosen here and stated, not
  checked against a published table: `sqrt` ½ (correctly rounded by IEEE
  754), `exp`, `log`, `sin`, `cos`, `atan`, `asin`, `acos` 1, `tan`,
  `sinh`, `cosh`, `tanh`, `atan2` 2. glibc does not round these correctly,
  and its manual's test suite flags only errors above 9 units, so the
  figures are an assumption about the library, the one place the bound is
  not guaranteed by the model alone (open: measure them, or take the 9);
- the bound, computed in floating point, is widened by a relative `2⁻⁴⁸`
  and `4·2⁻¹⁰⁷⁴`, more than its own few roundings can lose.

A property test checks it over generated arithmetic (the four operations,
square roots, exponentials) against the affine backend's enclosure, 20000
cases clean before it went in.

*Stochastic arithmetic* (`samples N`). N copies run in lockstep; each
operation on each copy rounds the exact result to the double below or
above it, with equal probability, the side from the same error-free
transformations (a fused multiply-add through exact rationals for `fma`);
a library function's copy moves one unit in the last place up or down; a
literal's copies are its two neighbouring doubles when it has two. The
coin is a hash (SplitMix's finaliser) of the seed, the copy, the
operation and its operands, so an estimate does not depend on the order
lazy values are forced in. The estimate is `τ·s/√N`, the copies' sample
deviation scaled by Student's t at 97.5 % for `N − 1` degrees of freedom
(a table to 30, then its expansion about the normal). `:set samples`
takes 0 or 2 to 100000 (10⁵, for Monte Carlo; one copy has no spread).
`:set seed` defaults to 1.
Few copies can all agree by chance, and the value then prints as exact:
`0.1 + 0.2 + 0.3 + 0.4 + 0.7 - 1.7` at three samples is `0 ± 6.4e-16`
at seed 1 and `0` at seed 3, the method's known weakness at small N.

*Comparisons.* The IEEE result decides (`NaN` compares false, `/=` true).
Under samples, a comparison whose copies disagree is noted on the
evaluation's budget (`Metron.Limits.remark`, kept in place for the reason
the step counter is) and printed after the value: `warning: the
comparison 1 > 1 goes both ways across the 3 samples: the condition is
lost in rounding`. The design's wording names the `if`'s source; the
comparison and its operands are what the evaluator has.

*Printing.* The shortest digits that read back, written as Metron writes
numbers (scientific outside `[10⁻⁴, 10¹⁵)`), then `± e` to two digits,
rounded up for a bound, and once after the value `(bound)` or
`(estimate, 3 samples)`; an exact value prints alone. A display unit
divides the value and scales the estimate exactly, so `2 m * 3` prints `6
m`. A NaN or an infinity prints with its origin: `NaN (the first NaN came
from sqrt (-2))`. A value whose copies carry draws of a declared σ prints
its IEEE value with the sample beside it instead, `0 (Monte Carlo: mean
1.015, sd 1.441, 10000 samples)` (the corrections under "Declared σ is
sampled").

*Its built-ins*, the same under either setting: `errorOf x` (the
estimate, elementwise, in `x`'s dimension), `digitsOf x` (`−log₁₀(e/|x|)`,
from 0 to `log₁₀ 2⁵³ ≈ 15.95`), `ulps a b` (decided here: how many
doubles lie from `a` to `b`, for checks such as `ulps r expected <= 4`;
the size of one step is `nextUp x - x`), `eps` (`2⁻⁵²`, the gap from 1 to
the next double), `nextUp x` (a function of the double: its error is
`x`'s), `fma a b c` (one rounding), `isNaN`, `isInfinite`.

**Choosing.** `:backend` names the backend, `:backend double` switches,
`metron --backend double` starts under one. The built-ins only one
backend has are listed in `Metron.Scalar.backendOwn`: affine's `±`, `±σ`,
`noise`, `gauss`, `mid`, `sd`, `bound`, and `covariance` and
`crossCovariance` too, by the design's own criterion (they read
uncertainty, and under double they would be zeros); double's eight.
`:exact`, `:budget` and `:covariance` are refused under double.

**The check.** Core's one walk for references (`directUses`; `refs` and
`refsWithIndex` are now its projections) names the backend-specific
built-ins a term uses itself. `Metron.Needs` memoises `needs(h)` in the
session (`Session.needs`), extended as inputs reach new hashes and never
invalidated. Before an expression evaluates, its Core is walked and the
memo answers for its references; a failure finds the path down the
definitions that need the name: `` `orbitError` uses `sd` (through
`budgetOf`), which the double backend does not have ``. A direct use
gives the runtime's message, `` `sd` is the affine backend's; the double
backend does not have it ``, which the evaluator also gives should a
backend ever meet another's built-in. Commands that evaluate for
inspection (`:exact` and the others) and `:prefer`'s units are not
checked: the first are affine's, the second always run under affine.

**What it means for the library.** Definitions that carry a declared
uncertainty are affine's: CODATA's `G` (`` `G` uses `±σ` ``), the astro
bodies' measured constants, `astro.kepler`'s solvers (which use `mid`,
`bound` and `±` to keep their enclosures honest) and
`linalg.jointCovariance`. They are refused under double, as the design
intends; a double port of them is a separate decision.

**Not built.** `:trace`, open above. `samplesOf`. (`--set` now takes
every setting `:set` does, `samples`, `seed` and `rounding` included: see
the as-built note under "Declared σ is sampled".)

## 9. Module layout and libraries

Library code in `lib/`, executable in `src/`, as `doc/style.md` requires.

```
lib/Metron/Syntax.hs           surface AST with source spans
lib/Metron/Lexer.hs            unicode normalisation and token mapping (2.8), layout rule
lib/Metron/Parser.hs           megaparsec; operator table; quantity rule; sections; where
lib/Metron/Desugar.hs          surface → Core (2.9): total, local, no types
lib/Metron/Resolve.hs          free names → refs, SCCs, cycle construction
lib/Metron/Core.hs             Core ABT with name hints; alpha-equivalence; substitution
lib/Metron/Dimension.hs        abelian group, normalisation, Kennedy unifier
lib/Metron/Type.hs             types, schemes, pretty-printing of types
lib/Metron/Infer.hs            algorithm W over Core, generalisation per component
lib/Metron/Overload.hs         closed constraint solver and defaulting
lib/Metron/TCore.hs            Typed Core (5.3)
lib/Metron/Elab.hs             Core + inference results → Typed Core
lib/Metron/Hash.hs             canonical encoding, SHA-256, cycle hashing
lib/Metron/Codebase.hs         terms, names, history; the operations of 7.1
lib/Metron/Store.hs            on-disk layout of 7.4
lib/Metron/Value.hs            runtime values
lib/Metron/Affine.hs           magnitudes: exact and affine forms, arithmetic, compaction
lib/Metron/Transcendental.hs   series evaluators with rigorous error bounds
lib/Metron/Linear.hs           vector and matrix kernels over magnitudes
lib/Metron/Metron.hs             the interpreter over Typed Core
lib/Metron/Units.hs            base dimensions, prelude generator
lib/Metron/Budget.hs           nudge attribution by kind, covariance view
lib/Metron/Pretty.hs           values, Core → surface text (unicode or ASCII), digits
lib/Metron/Repl.hs             haskeline loop and : commands
src/Main.hs                  CLI modes
data/prelude.metron              generated units and constants
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
3. **Affine magnitudes.** `Metron.Affine` (magnitudes, rigorous elementary
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
   A joint state covariance as homogeneous blocks (§3.7): done, with
   `crossCovariance`, the library's `Cov2` and its filter steps, and
   `:covariance (r, v)`.
   Points and charts (§3.6): done, over any shape; charts with a parent: done,
   translated and turned by constant generators, and moving charts with a
   declared spin, composed through the tree, with states in `astro` (§3.8).
   Since §3.10's part F a point is typed and stored by its frame, and a chart
   sits on a declared space.
5. **Mutual recursion.** SCC analysis, cycle hashing, group inference.
6. **Persistence and REPL polish.** User and project-local stores, haskeline, all
   `:` commands, error messages with source spans. Status: stores done (§7.4),
   haskeline with a history file beside the store, `:store`, `:prefer`,
   `:covariance`, `:set unicode` (§7.3), and `metron --merge OTHER` to merge two
   stores (§7.4). Nothing remains here.
7. **Tuples**, then **lists** with a `case` construct in the core. Status: done.
   `Con` and `Case` replaced `If` and the boolean literal (core.md §5). User
   data types (§2.3): done, as the same mechanism with declared constructors,
   kinded parameters inferred from use, self-recursion, owner-stamped or
   structural identity, and persistence in `types/`. Records: done, as field
   labels on one-constructor types with `b.f`, `C {f = e}` and `b {f = e}`
   desugaring to `case`; record values print with their field names.
   `Bool`, tuples and lists are library declarations the compiler holds
   (§2.3, item 9). Remaining: mutually recursive types.
8. **Later.** Named projection positions as a scoped sugar (`.x .y .z`,
   `.pos .vel`, §2.10); precision refinement for undecidable comparisons
   (re-evaluate at higher `p`); mixed-dimension matrices
   in the type system (§3.7.1), should blocks stop being enough; ball-plus-zonotope enclosures for
   radial bounds; non-SI and affine-offset units (°C); rewrite rules that
   fuse `star (wedge a b)` back into a hand-coded 3D cross kernel and notice
   when only part of a product is consumed (laziness already avoids the
   arithmetic, not the allocation); compilation for long
   propagations.

9. **Design first, then delegate.** Each of these needs a decision written
   down before any code; once it is, the implementation is routine enough to
   hand off.
   - *Mixed-dimension matrices.* Decided (§3.7): a joint position-velocity
     covariance is a record of homogeneous blocks (route B, built), and
     Hart's dimensioned matrices (route A) are written down rule by rule,
     with what building them takes. Route A is not to be started until the
     escalation signal of §3.7.2 appears: block formulas beyond 2×2 blocks,
     or the inverse of a single matrix of mixed dimensions.
   - *Charts: frames with an orientation.* Designed in §3.8: one chart value
     (step, origin, a bivector generator), rotations as `exp` of the
     generator with an exact inverse, every other description sugar to a
     bivector, moving charts as functions of an epoch, the transport terms
     from a declared angular velocity. Built: constant orientations (`by B
     then B …`), moving charts (`chart ecef t on eci by … spinning ω`) and states
     (`astro.velocityIn`, `astro.stateFrom`); an Earth chart is the owner's
     decision (§3.8, open).
   - *Axis sets as index types.* §3.9, layer 2, decided with charts and
     built through stage 3: a shape position is a length and a name slot;
     `forall` is required in signatures and ascriptions, with sized binders
     and scoped variables, and printed by `:type`, `:ls` and written-back
     signatures; charts mint axis sets. Stage 3 (§3.10): part U, units as a
     syntax, with an implicit one at an operand of `*` and `/`; part F,
     spaces and frames: points typed and stored by frame, `space`, `chart …
     on …` with clauses, `from … to`, `on`, conversions through the shared
     configuration, and space constraints in inferred types. Layer 1, the `axes x y z` sugar, can be built any time.
   - *Precision refinement for undecidable comparisons.* Re-entering
     evaluation at a higher precision cuts across the evaluator's
     architecture (§3.2.9).
   - *`Bool`, tuples and lists as library declarations.* Decided and built.
     The three types are structural declarations
     the compiler holds as values and refers to by hash (`Metron.Builtin`):
     `structural data Bool = False | True`, `structural data Pair a b = Pair
     a b`, `structural data List a = Nil | Cons a (List a)`, and a tuple of
     `k` components, up to 32, the structural type of one constructor with
     `k` fields, so `(a, b, c)` is one constructor with three fields rather
     than nested pairs. `ConRef` lost `Builtin`; the type language lost
     `TBool`, `TTuple`, `TList` for `TData` on the hashes; the desugarer,
     the primitive type table, inference, lint, the evaluator and the
     printers (which still print `true`, `(1, 2)`, `{1, 2}`, `Bool`, `(a,
     b)` and `{a}` for those hashes) go by hash, never by name. The library
     seeds the same three declarations and names them under `std` (§7.7);
     renaming or unnaming them changes nothing but printing. Core keeps its fifteen
     constructors (core.md §5): what left was the built-in alternative of
     the constructor reference and three forms of the type language, not
     term constructors. Mutually recursive types stay open.
   - *Type annotations.* Decided and built (§4.8): a signature `name ::
     type` is label-level, checked after inference as an instance of the
     inferred scheme, and seen by uses of the name; the error says the
     definition's type is not as general as the signature. An ascription
     `(e :: type)` narrows by unification and does not reach Core.
     Polymorphic recursion stays out (§4.6); §11 has what is open.
   - *A brick front end*, `metron --tui`, beside the line REPL: the canonical
     echo live as you type, completion as a popup, multi-line editing, and
     room for panes (a `:ls` sidebar, the error excerpt beside the input).
     Built on the same `Metron.Repl` logic so the two never drift; the line
     REPL stays the default and the only front end for piped scripts and
     tests. `brick` and `vty` come in through `build-depends` via
     `callCabal2nix`.

---
10. **Codebase as the single truth.** In order, each on the last: namespaces
    and `:export` (§7.6, done); the standard library seeded under `std` with
    a stored `use std` (§7.7, done: seeding, `:use`, `:uses` and `:unuse`
    for stored uses, the bare `:ls`
    by namespace, the `:stdlib upgrade` sketch, and owner stamps by full
    path with re-hashing renames), then split by domain into `std`,
    `linalg`, `si`, `time`, `angle`, `temperature` (the six stored uses),
    `astro`, `physics` and `imperial` (§7.7, done); `:edit` as an editor round trip
    (§7.3): export the codebase, a namespace or one definition to a file,
    open `$EDITOR`, and on return enter the file as one group and reconcile
    it against the scope, adding, updating (with propagation) and unnaming
    as a text diff can tell, all or nothing, with the temp file kept on
    error (done: `:edit`, `:edit namespace`, `:edit name` and `:edit --file`,
    with the no-editor fallback; §11 has what is left). Upgrading a
    codebase from a newer library or another codebase
    stays open (§7.7).


## 11. Open questions

- Lazy precision (an idea for later; §3.2.8, §8.1). Today a value is computed
  once at the session's working precision `p`. Instead, a value could be a
  lazy, shared list of ever-better approximations, each element being
  exactly what today's evaluator gives at that precision, an affine form at
  `p₀`, `2·p₀`, `4·p₀`, …. A consumer (printing to n digits, a comparison,
  `floor`) walks the list until the value is good enough, and every other
  consumer of the same node shares the levels already forced.
  - A leaf whose terms are exact (the series of `exp 1`, Newton's iterates
    for `sqrt 2`) resumes where it stopped.
  - A function of an approximated input advances in plateaus. At one
    approximation of its input, its own series can only reach the error the
    input brings (`|f′(y)|·err_y`). Going further pulls the input's next
    level and computes again. An addition formula (`exp y′ = exp y · exp
    δ`, `sin (y + δ)`, …) makes each new level a cheap correction rather
    than a restart.
  - Keeping affine forms within each level preserves what plain intervals
    would lose: named nudges, so `x - x` is exactly 0, the budget and σ.
    It also tells a consumer when to stop: walk on while the width is
    rounding, stop at once when it is declared `±` or `±σ`, which no
    precision shrinks.
  - The cost over today is bookkeeping and memory, the levels a node keeps
    while it is alive, and it is paid only where a consumer asks for more
    than `p`. A `max precision` limit (§8.1) would cap the walk, since equal
    values never separate.
  - The simpler alternative is Ziv's strategy (Arb, MPFR): re-evaluate the
    whole term at doubling precision. It costs at most about twice the
    final run, but shares nothing between consumers that want different
    accuracy and never resumes a leaf.
- `:sample expr` (§3.2): Monte Carlo over the statistical nudges, for a value
  marked non-linear, reporting quantiles rather than a mean and a σ.
- Curvilinear charts (§3.10). A chart is affine, so latitude and longitude,
  spherical coordinates and topocentric azimuth, elevation and range are
  functions today (`toGeodetic : Point ecef -> Geodetic`), not charts. A
  curvilinear chart would be defined by a pair of functions to and from an
  affine parent, `chart geodetic on ecef via toGeodetic fromGeodetic`: its
  points typed by frame (`Point geodetic`), `to` converting through the
  functions, and `.-` and `.+` refused, since a difference of coordinates on
  a curved chart is not an amount ("subtract on an affine frame: `b .- a on
  ecef`"). Worth building if conversions through such functions around `to`
  become common, as they may in iapetus.
- A frame per item of data (§3.10, F3). Frames are minted by declarations,
  so their number is fixed when the code is written, which the owner accepts
  for now. Bodies that come from data, a list of a hundred satellites,
  cannot each be declared, and one parameterised chart would make them one
  frame. The candidates: a scoped frame in the style of `runST` (`frame c =
  chart in body`, a rigid frame that may not escape its scope, so points
  leave it only converted); existential packages of a chart and its points
  (`data Body = forall c. Body (Chart c) {Point c}`), the general form, which
  needs existential types and the same escape check; and a run-time identity
  check, which gives up the checker's guarantee.
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
- Does iapetus commit the binary `.metron/` store, or export definitions to `.metron`
  source files (text, reviewable in diffs) and treat the store as a cache?
  Partly answered: `:export` (§7.4) writes the codebase as source that
  reads back to the same labels and hashes, so both can be committed; open
  is whether the store may then be dropped, which would lose history.
- Should `:view` of a stale reference print `x#a3f9k` (Unison style) or `#a3f9k`
  alone?
- Curvilinear coordinates as a declaration: a `coordinates polar = to toPolar
  from fromPolar` bundling the pair, so `v to polar` reads like `p to eci` and
  a position can print in polar on request (§3.8). Sugar over two functions;
  the inverse cannot be checked and `to` on it must stay distinguishable from
  the exact, affine `to` on a chart. Wait for a use before adding it.
- Equality on declared types is derived structurally when every field is
  comparable (§4.2), the rule tuples and lists follow. Still open: whether a
  type may opt out, or give its own equality (a fraction kept as an
  unreduced pair, which structural equality calls unequal to its reduced
  form).
- A shape whose lengths are all one `n`, at any rank (`[n]`, `[n, n]`, …),
  cannot be written: a shape is a list of lengths with a variable tail
  (§4.1). So `transformBy : Mat n n -> Tensor s d -> Tensor s d` checks its
  lengths when it runs (§4.3), the one primitive that does. A shape
  language with "every length is `n`" (`Tensor (n ^ k) d`, a length
  repeated a variable number of times) would make it a type error; wait
  for a second primitive that needs it.
- `==` on data evaluates every field even after one is unequal, so `Pair 1 (2 ± 0.1) == Pair 2 2` says "cannot decide" where false was knowable; tensors, tuples and lists do the same. Short-circuit, or keep the uniform rule?
- A root constructor named like a library unit (`data Temp = T …`) shadows
  the tesla `si.T` silently, as any root name shadows the library's (§7.7).
  Warn, or keep the shadowing rule?
- `:edit` (§7.3), what is left:
  - `:update` of a `data` type does not move the definitions that build or
    match its constructors; `:edit` does (`Metron.Update.propagateWith`).
    Should `:update` do the same?
  - A type outside the edited file whose fields use an edited type keeps
    the old one, and the report says so; `:rename` re-declares such a type
    (§7.2). Follow it here too, or ask for a wider scope?
  - A definition deleted from the file that another definition in the
    file still uses resolves to the codebase's version while the file is
    entered, so the user is left stale (and reported). Refuse that edit
    instead?
  - What does not round-trip through `:export` (§7.4) does not through
    `:edit`: two labels on one stamped or recursive reference, and a
    stamp that no longer matches its path, report as updated from an
    unchanged file.
  - A changed keyword on an unchanged body (`unit km` to `let km`) is
    applied and reported, but the store's log has no line that clears a
    `unit` or `chart` flag, so after a restart the name is a unit again.
    `:update` has the same gap.
- Type annotations (§4.8), what is left:
  - A definition that uses a signed name keeps its Core's type: `let h y =
    f y` with `f :: Num m -> Num m` is `a -> a`, so `h (3 s)` works
    where `f (3 s)` is refused. Stored types are a function of the hash,
    which cannot see labels. Should such a definition be given the narrower
    type it was checked at as a signature of its own (label-level, and so
    stored), or should a use through it be refused some other way? An
    ascription inside a definition has the same limit: it checks, and the
    definition keeps its Core's type.
  - Propagation re-checks a moved dependent without the signatures its
    references see, only against its own signature.
  - Polymorphic recursion (§4.6).
- Provenance paths (§4.7) and the paths inference walks disagree inside
  `case` alternatives (a body is one level deeper in inference), `if`
  branches (also swapped) and list literals (elements are nested `Cons`
  nodes), so a type error deep inside one of those gets the definition's
  span, or sometimes another node's (`case x of true -> sin (1 m); …`
  points at the `1`). Fixing it moves error excerpts of existing inputs,
  so it is left for a change of its own; ascriptions do not depend on it
  (§4.8).

---

## 12. Worked scenario: iapetus

An illustrative session with `:set precision 6` for brevity. Numbers are rounded for
the page; the real output follows the printing rules of §3.2.10 exactly.
The constants live in `astro`, which a seeded codebase does not use by
default (§7.7), so the session starts by storing that use.

```
> :use astro
stored use astro
> let mu = iers2010.earth.mu
> :type mu
Num (m^3/s^2)
> mu
398600441800000 ±σ 800000 m^3 s^-2     -- IERS TN36 Table 1.1, with its σ

> let period a = 2 * pi * sqrt (a^3 / mu)
> :type period
forall d. Num (d^2/m) -> Num (s*d^3/m^3)   -- a signature narrows it: Num m -> Num s
> period (7000 km) to min
97.141943967 ±σ 9.7e-8 (bound 5.7e-9) min
> :budget period (7000 km)
5828.5166380 ±σ 5.8e-6 (bound 3.4e-7) s
  kind   source               contribution  share
  σ      iers2010.earth @0.0  5.8e-6 s      100% of σ²
  bound  mul                  1.8e-7 s      52% of bound
  bound  recip                1.3e-7 s      39% of bound
  bound  pi                   1.9e-8 s      6% of bound
  bound  sqrt                 1.3e-8 s      4% of bound

> let vis_viva r a = sqrt (mu * (2 / r - 1 / a))
> vis_viva (7000 km) (7000 km) to km/s
7.5460532900 ±σ 7.6e-9 (bound 1.1e-10) km s^-1

> kepler.period iers2010.earth (7000 km) to min   -- the library's: a body names the constants
97.141943967 ±σ 9.7e-8 (bound 5.7e-9) min

> let rotz t = [cos t, -(sin t), 0; sin t, cos t, 0; 0, 0, 1]
> :type rotz
forall (a : 3) (b : 3). Num rad -> Mat a b   -- a literal's axes come from use (§3.9)
> rotz (90 deg) @ [1, 0, 0] km
[1.9e-25 ± 1.9e-25, 1.0000000000000000000…, 0] km   -- the series' enclosure of cos (π/2)
> let t = 45 deg ± 0.001 rad in rotz t @ [1, 0, 0] km
[0.70711 ± 0.00071, 0.70711 ± 0.00071, 0] km
> let t = 45 deg ± 0.001 rad in norm (rotz t @ [1, 0, 0] km)
1.00000025 ± 9.6e-7 km                  -- the angle error nearly cancels; a bound, not a sigma

> let x = 5 ± 0.1 in x - x
0

> let e = gauss 6
> let r = [7000, 0, 0] km + Lr @ e      -- Lr : Mat 3 6 m, a covariance factor
> let v = [0, 7.5, 0] km/s + Lv @ e
> :covariance (r, v)                    -- the blocks of jointCovariance (3.5, 3.7)
rr [… ; … ; …] km^2
rv [… ; … ; …] km^2 s^-1
vv [… ; … ; …] km^2 s^-2
bound box ([0, 0, 0] km, [0, 0, 0] km s^-1)

> let kepler_E m e = newton_E m e 50 ± 1e-12    -- a solver declaring its tolerance
```

After the IERS publishes a new GM⊕, the set's definition is entered again
under `astro.iers2010` (or a newer library brings it with `:stdlib upgrade`,
§7.7); a root `let earth` would only shadow it:

```
> namespace astro.iers2010
…   let earth = astro.Body {mu = (3.986004418e14 ±σ 4e5) * 1 m^3/s^2, …}
…
> :update
updated earth #b7x2q -> #q2m8d
upgraded mu #c40ue -> #p91sm
upgraded period #e51ka -> #0dn4r
upgraded vis_viva #ap2z1 -> #7hc9w
> :history mu
#p91sm  (current)
#c40ue
```

Every dependent moved because each still typechecks against the new `earth`; the
report says so, one line per definition, and history keeps the old versions
reachable. Had a dependent stopped checking, it would have stayed on `earth#b7x2q`,
`:view` would show that, and `:todo` would list it until its author fixed it and
ran `:upgrade astro.iers2010.earth`. Nothing changes silently in either direction.

### A filter step in blocks

One step of a Kalman filter on the state `(r, v)`, with the joint
covariance as the blocks of §3.7. Unlike the session above, this one is not
rounded for the page: the lines are the test suite's (`filterStep` in
`test/Main.hs`, test "design §12: a filter step in blocks"), and every output
is copied from what that test checks, so it stays true. The precision is
the default. The `…` are the printer's mark for an exact value cut short
(§3.2.10): everything here is exact, since `±σ` puts the uncertainty in
the nudge coefficients and the filter is linear in them.

A position known to 1 km and a velocity known to 1 m/s, both standard
uncertainties, then the position 10 s on. `r1` and `v0` now share the
velocity's nudges, so their cross-covariance block is not zero: `10 s ×
(1 m/s)² = 10 m²/s` on each axis, in the unit of a position times a
velocity. The position's variance is `(1 km)² + (10 s × 1 m/s)²`:

```
> let eye = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
> let r0 = [7000, 0, 0] km ±σ 1 km
> let v0 = [0, 7.5, 0] km/s ±σ 1 m/s
> let r1 = r0 + v0 * (10 s)
> let p1 = jointCovariance (r1, v0)
> p1.rv
[1e-5, 0, 0; 0, 1e-5, 0; 0, 0, 1e-5] km^2 s^-1
> :covariance (r1, v0)
rr [1.0001, 0, 0; 0, 1.0001, 0; 0, 0, 1.0001] km^2
rv [1e-5, 0, 0; 0, 1e-5, 0; 0, 0, 1e-5] km^2 s^-1
vv [1e-6, 0, 0; 0, 1e-6, 0; 0, 0, 1e-6] km^2 s^-2
bound box ([0, 0, 0] km, [0, 0, 0] km s^-1)
```

Propagation over 60 s with the constant-velocity `Φ = [I, Δt I; 0, I]`. The
zero block has the dimension of `Φ_vr`, `s^-1`. The block result agrees
exactly with the covariance of the propagated state read off its nudges,
and the position's variance is now `(1 km)² + (70 s × 1 m/s)²`:

```
> let dt = 60 s
> let phi = (eye, dt * eye, [0, 0, 0; 0, 0, 0; 0, 0, 0] s^-1, eye)
> let p2 = propagateCov2 phi p1
> p2 == jointCovariance (r1 + v0 * dt, v0)
true
> p2.rr
[1.0049, 0, 0; 0, 1.0049, 0; 0, 0, 1.0049] km^2
> p2.rv
[7e-5, 0, 0; 0, 7e-5, 0; 0, 0, 7e-5] km^2 s^-1
```

A range measurement along x with a 10 m standard uncertainty: `H_r` is a
`Mat 1 3`, `H_v` a zero `Mat 1 3 s`, and `R` a `Mat 1 1 (m^2)`. The
innovation covariance, the gain (a dimensionless `K_r` and a `K_v` in
`s^-1`), and the updated blocks:

```
> let h_r = [[1, 0, 0]]
> let h_v = [[0, 0, 0]] s
> let r_meas = [[(10 m)^2]]
> let s_innov = innovationCov2 h_r h_v p2 r_meas
> s_innov
[[1005000]] m^2
> let k = gain2 h_r h_v p2 (inverse s_innov)
> k
([0.99990049751243781094…; 0; 0], [6.9651741293532338308…e-5; 0; 0] s^-1)
> let p3 = updateCov2 k h_r h_v p2
> p3.rr to m^2
[99.990049751243781094…, 0, 0; 0, 1004900, 0; 0, 0, 1004900] m^2
> p3.rv to m^2/s
[0.0069651741293532338308…, 0, 0; 0, 70, 0; 0, 0, 70] m^2 s^-1
> p3.vv to m^2/s^2
[0.99512437810945273631…, 0, 0; 0, 1, 0; 0, 0, 1] m^2 s^-2
> transpose p2.rv - snd k @ (h_r @ p2.rr + h_v @ transpose p2.rv) == transpose p3.rv
true
```

The x variance falls from `1004900 m²` to `1004900 · 100 / 1005000 ≈ 99.99
m²`, the y and z blocks are untouched, and the velocity's x variance falls
too, through the correlation the propagation built. The last line checks
the block the record does not keep: the lower-left block of `(I − K H) P`,
computed directly, is the transpose of `rv`, exactly.

### A perifocal chart

An orbit's perifocal frame is eci turned by the 3-1-3 sequence of the
node, the inclination and the argument of periapsis (§3.8). Like the filter
step, the lines are the test suite's (`perifocalSession` in
`test/Main.hs`, test "design §12: a perifocal chart") and every output is
copied from what that test checks; the precision is the default. Ω = 30°,
i = 45°, ω = 60°, and the chart's step is the kilometre:

```
> space GCRS = Vec 3 m
> chart eci on GCRS
> chart pf on eci step km by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)
> :view pf
chart pf on eci step km by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)
> let rp = [7000, 0, 0] pf
> rp to eci
[887785.38831025442775…, 5462310.6012293745031…, 4286607.0498705616718…] eci
> (rp to eci) to pf
[6999.9999999999999999…, -1.3e-20 ± 8.9e-20, 6e-21 ± 2.4e-20] pf
```

Periapsis lies on the perifocal x axis 7000 km out; in eci it is 7000 km
times the first column of `euler313 (30 deg) (45 deg) (60 deg)`. Read back
on `pf`, by the generators negated in reverse order, it encloses `[7000, 0,
0]`: the components that are zero come back as enclosures of zero, which
is why a round trip is tested with `bound`, not `==`.

The velocity at periapsis is along the perifocal y axis. An amount's type
carries its axes (§3.9): the literal is taken along `pf`'s, `Vec pf
(km/s)`, and `from pf to eci` turns it to eci's, which are the space's base
axes, a `Vec GCRS (m/s)`, by the rotation alone (§3.10, F10). A
covariance known along the perifocal axes (radial 1 km, along-track 2
km, normal 3 km) goes the same way, as `R P Rᵀ`, by `rotateCov` with `pf`'s rotation, a `Mat GCRS pf`. It is
written in place: a value named by `let` is anonymous until given a frame
(§3.9, decision 5), and `rotateCov` would refuse it, with a hint, as a
frame mix-up.

```
> let vp = [0, 7.5, 0] km/s from pf to eci
> vp to km/s
[-6.9508252147247766082…, -0.95119863033241545830…, 2.6516504294495532165…] km s^-1
> rotateCov (rotationOf pf) ([[1, 0, 0], [0, 4, 0], [0, 0, 9]] km^2) to km^2
[4.5767451288348659649…, -1.3794313182928119555…, 1.0170048711651340350…; -1.3794313182928119555…, 4.0482548711651340350…, -3.5986214154904359879…; 1.0170048711651340350…, -3.5986214154904359879…, 5.3749999999999999999…] km^2
> rp.0
7000 km
```

The trace is still 14 km², as a rotation keeps it. A point is held in its
frame's coordinates (§3.10, F6), so a coordinate of a point on a turned
chart is an amount along that chart's own axis, the step applied: `rp.0`
is `7000 km`, exactly.

### A spinning Earth

A ground station turns with the Earth, and its velocity in eci is the
Earth's rotation alone (§3.8). The library ships no Earth chart, so the
session defines a simple one for illustration only: it ignores precession,
nutation, polar motion and UT1 − UTC, and puts the station on a sphere, so
its positions are off by tens of kilometres. Precession alone, about 0.36°
since J2000 by 2026, moves a point on the equator about 40 km, and the
sphere puts this station about 25 km from its WGS84 place (`[3980.7, 0,
4966.8] km` for latitude 51.4769° at sea level). The angle is a linear
GMST from J2000.0 (Meeus, *Astronomical Algorithms*, without the T² and T³
terms of the IAU 1982 expression), and the spin is the same rate, so the
two agree by construction. At 2026 Jan 1 0h UT1 it is 100.6608323° modulo
360°, 0.094″ short of the IAU 1982 GMST (Aoki et al. 1982, A&A 105, 359),
100.6608585°, which the test checks. As before, the lines are the test suite's
(`spinningEarthSession`, test "design §12: a spinning Earth, for
illustration") at the default precision:

```
> space GCRS = Vec 3 m
> chart eci on GCRS
> let gmst t = 280.46061837 deg + 360.98564736629 deg / day * (t .- 0 J2000)
> chart earth t on eci by rotz (gmst t) spinning [0, 0, 360.98564736629] deg/day
> :view earth
chart earth t on eci by rotz (gmst t) spinning [0, 0, 360.98564736629] deg / day
> chart greenwich t on (earth t) at [3972.5, 0, 4990] km
> let t26 = 9496.5 J2000
> [0, 0, 0] (greenwich t26) from (greenwich t26) to eci
[-734892.0553385001942 ± 3e-13, 3903932.6219852148939…, 4990000] eci
> :use astro
stored use astro
> let st = stateFrom (greenwich t26) t26 ([0, 0, 0] m) ([0, 0, 0] m/s)
> st.vel to m/s
[-284.67928970827302009…, -53.589180086727794658 ± 2.2e-17, 0] m s^-1
> velocityIn (greenwich st.epoch) st
[0, 0, 0] m s^-1
> velocityIn (greenwich t26) (State {epoch = t26, pos = st.pos, vel = [0, 0, 0] m/s})
[0.00000000000000000 ± 4e-17, -289.67930235205722039…, 0] m s^-1
```

`greenwich` is a moving chart under a moving chart: its time is passed to
`earth`, its parent. A point on it converts from the configuration named
with `from`, never the one it was written with (§3.10, F7): `[0, 0, 0]
(greenwich t26) to eci` is refused, "greenwich takes arguments: write [0,
0, 0] (greenwich t26) from (greenwich …) to eci". `st` is a `State J2000
GCRS`, its epoch a `Point J2000` and its position a `Vec GCRS m`,
an amount from the space's base origin along its base axes: a state is
typed by its epoch's frame and its space's base axes (§3.10, part F, as
built), whatever chart it was made from. `velocityIn (greenwich t26) st` is
a `Vec earth (m/s)`, since a translated chart shares its parent's axes and
`earth t` has one frame and one axis set, `earth`'s, for every `t`. At that
epoch the station is at right ascension 100.66° in eci, 3972.5 km from the
axis, and `stateFrom` gives it `ω × r`, 289.68 m/s (`7.2921158553e-5 s⁻¹ ×
3972.5 km`) eastward, with no velocity of its own. Read back on its own
chart it is at rest. A body at rest in eci passing the station moves west
on the station's chart at the same speed: the transport terms, `−v_o − ω ×
(p − o)` turned onto the chart's axes, are all of its velocity there.

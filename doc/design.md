# Design: `metron`

A small, pure, unit-aware, content-addressed calculator language.

This document is the specification of the project. It fixes the syntax, the value model, the type system, the nominal form that is hashed, the codebase model and the evaluation, and it lists the work still to do. Code follows it. When the code and this document disagree, change one of them deliberately. [overview.md](overview.md) is the entry point: it has the pipeline, the module map, the feature map and a glossary.

**How to read it.** Each subsection states its rules as behaviour that can be checked in the code or by running Metron. Each one ends with two lines:

- **Implemented in:** the modules, and in parentheses their key functions, that hold the rules.
- **Tested by:** the test groups that check them, as tasty names in quotes. ` › ` joins a group to a group or case inside it. Run one with `cabal test --test-options='-p "/name/"'`.

Two marks show the status of a rule:

- **Decided.** The owner decided this. Change it only with the owner.
- **Open.** Not decided, or not built. The item points to §10 (pending work) or §11 (questions for the owner).

Section numbers are stable. Code comments and test names cite them (`design §3.2.8`, `§3.10, F7`), so a new section takes a new number and no section is renumbered.

## Contents

1. Goals and non-goals: 1.1 Uses, 1.2 Goals, 1.3 Non-goals, 1.4 Architecture
2. Surface syntax: 2.1 Lexical structure, 2.2 Statements and layout, 2.3 Expressions, data types and records, 2.4 Tensor literals, 2.5 Operators, 2.6 The quantity rule, 2.7 Grammar, 2.8 Unicode spellings, 2.9 Desugaring, 2.10 Component access and qualified names
3. Values, numbers and units: 3.1 The value universe, 3.2 Magnitudes (3.2.1 to 3.2.12), 3.3 Vectors, matrices and tensors, 3.4 Error on compound values, 3.5 Covariance, 3.6 Points and charts, 3.7 Mixed dimensions, 3.8 Charts: frames with an orientation, 3.9 Axis sets, 3.10 Units, spaces and frames (Part U: U1 to U9, Part F: F1 to F10)
4. Type system: 4.1 Types, 4.2 Products, shape constraints and the instances, 4.3 Types of the primitives, 4.4 Dimension unification, 4.5 Inference, 4.6 Known limitations, 4.7 Error reporting, 4.8 Type annotations
5. Core and Typed Core: 5.1 Core, 5.2 The nominal form, 5.3 Typed Core
6. Hashing: 6.1 Canonical encoding, 6.2 Hashing cycles, 6.3 Dependency analysis
7. Codebase and names: 7.1 Model, 7.2 Versioning is relabelling, 7.3 REPL commands, 7.4 CLI and persistence, 7.5 Scratch, add, update, upgrade, 7.6 Namespaces, 7.7 The standard library
8. Evaluation: 8.1 Resource limits, 8.2 Backends (8.2.1 to 8.2.9)
9. Module layout and libraries
10. Roadmap
11. Open questions
12. Worked scenario: iapetus (12.1 to 12.5)

---

## 1. Goals and non-goals

### 1.1 Uses

Two concrete uses drive every priority in this document.

**A quick CLI calculator that understands units.** A user types
`metron '5 km/h to m/s'` every day. The calculator gives exact answers,
handles units without ceremony, and starts at once.

**A function library for the iapetus project.** iapetus is the owner's
orbital-mechanics project. It needs functions that carry units, work on
vectors and matrices, and track how approximation error and input
uncertainty build up through user-defined functions. The library needs
stable versioning of definitions over years.

**Implemented in:** `Main` (`options`), `Metron.Driver` (`feed`, `feedFile`), `Metron.Prelude` (`stdlibSource`).
**Tested by:** "end to end"; "astro (design §7.7)".

### 1.2 Goals

- Exact arithmetic by default: `1/3 * 3` is `1`, not `0.9999…`.
- Units of measure are checked statically. `1 m + 1 s` is a type error, not a
  surprise at run time.
- Expressions are pure and bindings are immutable, with Haskell-like
  semantics.
- Input distributions propagate through arbitrary user code by Monte Carlo sampling.
  Double rounding sensitivity is analyzed separately (§3.2).
- Vectors, matrices and tensors are first-class dimensioned values (§3.3).
- Every definition has a nominal form with a content hash. Names are labels
  that point at hashes. Versioning is label management, as in Unison (§7).
- Interactive use (the REPL) and one-shot use (`metron 'expr'`) are both
  supported (§7.3, §7.4).

**Implemented in:** `Metron.Rational` (`addM`, `mulM`), `Metron.Infer` (`elaborateClosed`), `Metron.Hash` (`hashTerm`), `Metron.Codebase` (`bindName`), `Metron.Driver` (`feed`).
**Tested by:** "separate sampling foundation"; "units"; "hash"; "codebase"; "end to end".

### 1.3 Non-goals

- Strings, general type classes, IO and effects. Data types and lists exist
  (§2.3), but nothing consumes text.
- Temperature scales as units. °C and °F are affine, not multiplicative, so
  they are charts for points (§3.6), never units.
- Vectors or matrices whose components have different dimensions. A matrix of
  mixed dimensions is a record of homogeneous blocks (§3.7).
- Performance beyond "interactive for a few thousand steps" (§9).
- Unit systems beyond the SI, the units the SI accepts, and the small
  `astro`, `physics` and `imperial` sets of the standard library (§7.7).

**Implemented in:** not applicable: these are things the implementation does not do.
**Tested by:** not applicable.

### 1.4 Architecture: three representations

The implementation is organised around three representations of a program,
in the spirit of GHC's source, Core and STG split. Each has one job.

```
  source text
      │  lex (unicode → canonical tokens), layout, parse
      ▼
  Surface AST          rich: unicode, sugar, sections, where, superscripts, spans
      │  desugar, resolve names → refs
      ▼
  Core                 small, named-with-hints, untyped: this is what is hashed
      │  infer, elaborate (explicit type abstraction and application)
      ▼
  Typed Core           System-F-like, checked by lint
      │
      └─▶ evaluator, generic over a scalar backend: affine or double (§8.2)
```

- **Surface AST** (§2) is a faithful tree of what the user typed, with source
  spans for error messages. Everything convenient lives here and nowhere
  else.
- **Core** (§5) is the desugared language: fifteen constructors,
  one-parameter lambdas, resolved references, no operators and no sugar.
  Binders keep a *name hint* that hashing and equality ignore. The content
  hash (§6) is computed from Core, so the identity of a definition does not
  depend on its types. This is Unison's choice, and it keeps hashes stable
  when the type system grows.
- **Typed Core** (§5.3) is Core after inference and elaboration. Every binder
  is annotated, type, length, shape, dimension and axis abstraction and
  application are explicit, primitives carry the type they are used at, and
  defaulting is done. `lint` checks it independently before anything is
  stored or evaluated. It is derived data: the codebase keeps it beside the
  Core hash in memory and recomputes it when a store loads (§7.4). The
  evaluator (§8) runs it.

The pretty-printer goes the other way, from Core to surface text, and emits
either unicode or ASCII spellings (`:set unicode on|off`, §7.3).

**Implemented in:** `Metron.Lexer` (`tokenize`), `Metron.Parser` (`parseProgram`), `Metron.Desugar` (`desugarDefinition`), `Metron.Resolve` (`processGroup`), `Metron.Infer` (`elaborateClosed`), `Metron.Check` (`checkCore`), `Metron.TCore` (`lintClosed`), `Metron.Eval` (`evalClosed`), `Metron.Pretty` (`renderTerm`).
**Tested by:** "end to end"; "typed core"; "properties".

---

## 2. Surface syntax

The surface language is close to Haskell, with a unicode layer and a handful
of calculator-specific sugars. Desugaring (§2.9) removes everything in this
chapter, so the type checker never sees it.

### 2.1 Lexical structure

- **Identifiers**: a letter or `_`, then letters, digits, `_`, `'`, and
  subscript digits (`v₀`, `e₁`). Any Unicode letter is allowed, so `Ω`, `µ`,
  `θ` and `Δv` are identifiers. Source is NFC-normalised, and the
  compatibility confusables are folded: `µ` U+00B5 becomes `μ` U+03BC, and
  `Ω` U+2126 becomes `Ω` U+03A9. ASCII aliases exist for every prelude unit
  that needs one (`ohm`).
- **Numbers**: `3`, `9.81`, `1e-3`, `6.674e-11`, `1_000_000`. A number literal
  is always an exact rational: `9.81` is exactly 981/100. `1/3` is an
  expression, not a literal. Underscores are ignored. A literal whose decimal
  exponent is past the `digits` limit is refused by the lexer (§8.1).
- **Comments**: `--` to the end of the line, and `{- … -}` blocks, which nest.
- **Historical references**: a glued `name#hash` or a bare `#hash`, optionally
  followed by a glued `.index` for a member of a recursive group (§7.2). Hash
  prefixes use lowercase base32hex (`0-9`, `a-v`) and must identify a unique
  reference. An ambiguous prefix is refused with every full hash it matches.
  A bare hash as an application argument or after a quantity needs
  parentheses, as in `f (#hash)`, so that a trailing `#label` (§3.2.4) stays
  unambiguous: `f #hash` is read as a label and refused with "a #label must
  follow sample; `#hash` labels nothing here".
- **Keywords**: `let`, `in`, `where`, `if`, `then`, `else`, `to`, `true`,
  `false`, `unit`, `chart`, `space`, `on`, `from`, `at`, `case`, `of`, `data`,
  `namespace`, `use` and `forall` (also `∀`). `structural` is a word only
  before `data`. `as` in `use a as k` is not a keyword, because it is also the
  attosecond. `step`, `by`, `then` and `spinning` are clause words inside a
  chart statement only (§3.10, F10).
- **Operators**: `+ - * / ^ == /= < <= > >= && || :` and the others of
  §2.5, with their unicode spellings (§2.8). A name in backticks is an infix
  operator: ``a `dot` b``.
- **Statement separators**: a newline at indentation zero, or `;`. A line that
  starts with whitespace continues the previous statement.

**Implemented in:** `Metron.Lexer` (`tokenize`, `prepare`, `number`, `hashLabel`, `identifierOrKeyword`, `layout`), `Metron.NameResolution` (`historicalReference`).
**Tested by:** "lexer"; "codebase" › "hash references validate missing, malformed and ambiguous prefixes".

### 2.2 Statements and layout

A *program* is a file, a piped stdin, or one multi-line REPL input. It is a
sequence of statements. All statements in one input form a **binding
group**: they can refer to each other in any order, and mutual recursion is
possible only within a group. A REPL input of one line is a group of one. An
input that goes on at continuation lines (§7.3) is one group, as a file is.

```
let x = 2 + 3                   -- bind a name
let f x y = x * y + 1           -- sugar for: let f = \x y -> x * y + 1
f 3 4                           -- a bare expression: evaluate and print
```

A `let` without `in` at the top level *proposes* a definition. It goes into
the scratch (§7.5), where it is checked, hashed and usable by later
expressions, but not stored. The other declarations work the same way:

- `unit name = e` proposes a definition whose name is a display unit
  (§3.2.12, §3.10 U7).
- `chart name params… on parent [at origin] [step unit] [by B [then B …]]
  [spinning ω]` proposes a chart (§3.6, §3.8, §3.10 F10).
- `space Name = type` proposes a space (§3.10, F2).
- `data` and `structural data` propose a type (§2.3).

`:add` and `:update` move scratch definitions into the codebase (§7.5).
Within one input a name can be defined only once, as in a Haskell module:
"`a` is defined twice in the same group". Across REPL inputs, a newer input
replaces a pending definition, with the note "replaced pending definition of
`g`".

`name :: type` on a line of its own is a **signature** (§4.8). It gives the
definition of that name in the same input, before or after it, a type to be
checked against, written as `:type` prints types. It is a statement like the
others, so it can stand in a `namespace` block, where it signs the block's
definition of that name. A signature whose name has no definition in the
input, the scratch or the codebase stays pending, and `:add` refuses it:
"`g` has a signature but no definition; define it, or :forget g".

```
area :: Shape -> Num (m^2)
let area s = case s of Circle r -> pi * r^2; Rect w h -> w * h
```

`namespace a.b` followed by an indented block of statements puts what the
block declares under the path `a.b` (§7.6). Blocks nest. `use a.b` and
`use a.b as k` make the names of a namespace resolve bare, or under the
prefix `k.`, for the statements after it in its block. A top-level `use`
lasts for the rest of the REPL session, and a file read with `:load` keeps
its `use`s to itself. The statements of a `namespace` block and the `use`
form are part of the input's binding group like any other.

```
namespace orbital
  let mu = 398600.4418 km^3/s^2
  let period a = 2 * pi * sqrt (a^3 / mu)    -- mu is orbital.mu
use orbital
period (7000 km)
```

**Layout** is simpler than Haskell's, and has no parse-error rule:

- A token that starts a line at the column of its enclosing context starts a
  new statement, or a new `where` binding or `case` alternative.
- A token further right continues the previous one. So a multi-line
  `let … in` expression must indent the `in`, and a bracket that spans lines
  must indent its continuation lines.
- A `namespace` block opens at the first token after its path, as a `where`
  block does at the first token after `where`. That token must be indented
  further than the `namespace` line, or stand on the same line.
- A `namespace` with nothing under it is refused, so a forgotten indent cannot
  put the rest of a file into the namespace: "namespace foo has no
  statements: indent them under it, or write them on the same line".

**Implemented in:** `Metron.Parser` (`program`, `statement`, `letStatement`, `signatureStatement`, `namespaceStatement`, `useStatement`), `Metron.Lexer` (`layout`), `Metron.Resolve` (`processGroup`, `checkDuplicates`).
**Tested by:** "parser"; "lexer" › "layout: column-zero newlines separate statements"; "namespaces"; "type annotations".

### 2.3 Expressions, data types and records

```
\x y -> x + y                   -- lambda, one or more parameters
let a = 1 in a + a              -- local, non-recursive binding
if x > 0 then x else -x         -- conditional, both branches of one type
f a b                           -- application by juxtaposition, left-associative
(f a) b                         -- the same
```

`let … in`, `\ … ->` and `if … then … else` extend as far to the right as
possible, as in Haskell.

**Tuples, lists and `case`.** A tuple is `(a, b)` or `(a, b, c)`, with
components of any types. A list is `{a, b, c}` or `{}`, since brackets belong
to tensors (§2.4), and `x : xs` prepends. `case` takes both apart, one
constructor pattern deep:

```
case p of (r, v) -> r .+ v * dt            -- a pair
case xs of {} -> 0; x : rest -> x + sum rest  -- a list, two alternatives
if c then a else b   ≡   case c of true -> a; false -> b
```

- Alternatives are separated by `;` or by newlines at one indentation, as
  `where` bindings are.
- Every alternative is a constructor pattern with variables, or `_`, or a
  plain variable. Nested patterns are a parse error.
- A `case` must be exhaustive: `_` or a variable stands for every constructor
  not listed. A missing constructor is refused: "case does not cover Cons".
- Tuples have no projections. `fst` and `snd` are library definitions by
  `case`, and a six-element orbital state is `(r, v)` with two dimensions, not
  a `Vec 6`.
- Lists are the one unbounded structure. `map`, `filter`, `foldl`, `foldl'`,
  `foldr`, `length`, `zip`, `range` and `reverse` are library definitions in
  `std` (§7.7), recursive through `Cycle` like any other.

**The built-in types are declarations.** `Bool`, tuples and lists are not
built into the language. They are three `structural data` declarations that
the compiler holds as values and refers to by hash, which the declarations
alone fix:

```
structural data Bool = False | True
structural data Pair a b = Pair a b
structural data List a = Nil | Cons a (List a)
```

- `true`, `if`, `(a, b)`, `{a, b}` and `x : xs` are syntax for these
  constructors and for `case`, and print back as written, whatever names the
  types.
- A tuple of `k` components is the structural type of one constructor with
  `k` fields, and `Pair` is the case `k = 2`. A tuple has at most 32
  components, so that its type is known from its hash: "a tuple has at most
  32 components".
- The standard library names the three under `std` (§7.7), so `True`,
  `Pair 1 2` and `Cons 1 Nil` are `true`, `(1, 2)` and `{1}`, and
  `:view std.List` prints the declaration. Renaming or unnaming them changes
  only how a name prints.
- A user's `structural data Bool = False | True` is the same type. A nominal
  `data Bool` is refused: "`Bool` is a built-in type".
- A structural type is its shape, so any `structural data` of that shape is
  one of these. `structural data Color = Red | Green` is `Bool`, and `Red`
  prints `false`. A structural type of one constructor whose fields are its
  parameters in order, `structural data P a b = P a b` or a record
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

- **Fields.** A field is a type atom: a name (`Bool`, `Num`, a parameter, a
  declared type of no parameters) or a compound type in parentheses, written
  as `:type` prints it: `Num m`, `Vec 3 (m/s^2)`, `Mat 3 3`,
  `Tensor [2, 3] d`, `Point degC`, `Chart lvlh`, `Diff lvlh`, `(a, b)`,
  `{a}`, `a -> b`, `Maybe (Num m)`.
- **Lengths.** A length can also be `rank s` for a shape parameter `s`
  (§4.1): `data Idx s = Idx (Vec (rank s))`. `rank` is the one type-level
  function and cannot name a parameter.
- **Dimensions.** A dimension is a type argument (§4.1): one name bare
  (`Num m`, `Num N`, `Num d`), anything else in parentheses (`Num (m/s^2)`,
  `Num (km/h)`). Its names are base units (`m kg s A K mol cd rad`), declared
  units, which mean their dimension, and parameters. They are joined with `*`
  or `·` and `/`, with `^` or superscript exponents, parentheses and `1`.
  Square brackets are only ever a shape.
- **Kinds.** A parameter's kind is read off the positions it appears in, so it
  needs no annotation. A parameter used both as a dimension and as a type is
  refused.

**Constructors are functions and values.** `Circle` has type
`Num m -> Shape`, `Nothing` has type `Maybe a`, and `map Just xs` works.
Arguments are plain application: `Rect (3 m) (4 m)` passes two quantities,
while `Rect 3 m 4 m` passes four arguments, the metre twice among them
(§2.6). That input is refused with the unit message of §3.10 U3 and the hint
"3 and `m` are two separate arguments here; a quantity in argument position
needs parentheses: (3 m)". A `case` takes a value apart one constructor deep
and names the fields in order. `_` and variables fill in the constructors
not written, as for lists. Values print with each compound field in
parentheses, `Rect (3 m) (4 m)` and `Just (Circle (1 m))`, so that they read
back whatever their units. A record prints with its field names (below).

**Identity.** A type's identity is its definition: its parameter kinds, its
constructors' field types in order, and its full path as an owner stamp
(§3.2.4). So two users who declare `data Shape = …` alike, at the same path,
share one type, and `data Blob = Circle (Num m)` is another type.
`structural data` leaves the name out, so any two structural declarations
of the same shape are the same type.

**Names are labels.** Constructor names and the type name are labels in the
codebase, like definition names (§7):

- `:unname Circle` leaves the constructor printing as `#a3f9k.0`, and
  `:view Shape` prints the declaration back.
- A constructor name and a definition name share one namespace, and the newer
  label wins. Declaring `data Temp = T (Num K)` in `namespace si` unnames the
  tesla `si.T`. At the root it only shadows it, as any root name shadows the
  library's (§7.7).
- A declaration is pending in the scratch (§7.5) until `:add`, like a
  definition.

**Equality.** `==` and `/=` work on a declared type when every field of every
constructor has equality (§4.2), as on tuples and lists.
`Circle (1 m) == Circle (1 m)` is true, values built by different
constructors are unequal, and a type with a function field has no equality:
"no equality on Fn".

**Records.** A constructor can name its fields, which makes the type a
record:

```
data Body = Body {mass :: Num kg, pos :: Vec 3 m, vel :: Vec 3 (m/s)}
let b = Body {mass = 5 kg, pos = [1, 2, 3] km, vel = [4, 5, 6] km/s}
b.mass                              -- 5 kg
b {vel = [0, 0, 0] m/s}             -- the same body, stopped
Body (5 kg) ([1, 2, 3] km) ([4, 5, 6] km/s)   -- positional construction still works
```

- `b.mass` is a field access when the dot is glued to both sides (§2.10).
- `C {f = e, …}` with a constructor builds the record and must give every
  field once: "missing fields pos, vel".
- `e {f = e', …}` with anything else rebuilds `e` with those fields replaced.
- All of it desugars to `case` on the one constructor, so a record is an
  ordinary data type to Core and to the hash, and `:view` shows the `case`:
  `let gm x = x.mass` views as `gm = \x -> case x of B mass -> mass`.
- Field names are labels like constructor names, looked up by the field
  alone. So two record types cannot share a field name: the newer declaration
  takes it. `:unname .mass` removes one.
- Field names need a type with one constructor, so that `b.mass` is total:
  "field names need a type with one constructor".

A record value prints as it is built,
`Body {mass = 5 kg, pos = [1, 2, 3] km, vel = [4, 5, 6] km s^-1}`, which
reads back as the same value. The braces delimit each field, so no field
needs parentheses, and records nest:
`Pair {first = Body {…}, second = Just (Circle (1 m))}`. The printer sees
only the constructor's hash and index. The driver gives it the field labels
from the codebase, as it gives names for references (§7.2). A constructor
with no fields, or with any field unnamed (after `:unname .mass`), prints
positionally.

**Further sugar**, all removed by desugaring (§2.9):

```
let f x = x * k where k = 2          -- where: local bindings after a definition
(+ 1)   (2 *)   (`dot` v)            -- operator sections
a `dot` b                            -- infix application of a named function
f ∘ g                                -- composition, \x -> f (g x); also f . g with spaces
(3 m :: Num m)                       -- an ascription: narrows the type (4.8)
```

**Implemented in:** `Metron.Parser` (`caseExpr`, `patternP`, `listLit`, `dataStatement`, `sectionOp`), `Metron.Desugar` (`caseOf`, `recordExpr`, `fieldVar`), `Metron.Builtin` (`boolDef`, `pairDef`, `listDef`, `tupleDef`, `maxTupleArity`), `Metron.Type.Syntax` (`enterData`), `Metron.Pretty` (`renderValue`).
**Tested by:** "data"; "desugar"; "data" › "records: named fields, construction, access, update, printing"; "data" › "the built-in types are the structural declarations of their shape".

### 2.4 Tensor literals

```
[1, 2, 3]                       -- Vec 3
[1, 0; 0, 1]                    -- Mat 2 2, rows separated by ;
[[1, 0], [0, 1]]                -- the same matrix, nested
[1; 2]                          -- Mat 2 1, a column
[1, 2; 3, 4;; 5, 6; 7, 8]       -- Tensor [2, 2, 2]: ;; separates planes
[x, y, z] m                     -- Vec 3 m, by the quantity rule
```

- A literal is a bracketed list of expressions. Commas separate elements,
  `;` separates rows, `;;` separates planes, and so on.
- The rank is one more than the highest separator used. A level that never
  appears is a length-one axis, so `[1; 2]` is a 2×1 matrix, not a vector.
- The separator forms are sugar for nesting: `[1, 2; 3, 4]` is
  `[[1, 2], [3, 4]]`, and Core sees only the nested form.
- Values and `:view` print in the separator form too, except a tensor whose
  outermost axis has length one. `[[1, 2, 3]]`, a 1×3 matrix, stays nested,
  since the separator form reads back with a lower rank.
- Elements are separated by commas, never by spaces. Juxtaposition is
  application and the quantity rule, so `[sin x]` and `[2 pi]` keep the
  meaning they have outside brackets. Two literals side by side are refused:
  "a number next to a number: write the multiplication, 5 * 4".
- Components can be any expression. Every element must have the same shape
  and dimension, which the type checker enforces.
- The empty literal `[]` takes its element type from context (§3.3).

**Implemented in:** `Metron.Parser` (`vecOrMat`), `Metron.Desugar` (`foldConstant`), `Metron.Pretty` (`renderValue`).
**Tested by:** "parser"; "pretty"; "products".

### 2.5 Operators

From tightest to loosest:

| Level | Operators | Associativity | Notes |
|---|---|---|---|
| 13 | application, quantity rule | left | `f a b`, `3 m` |
| 12 | `^` | none | the exponent is an integer literal, optionally negative, so `^` cannot chain. A glued superscript is the same operator |
| 11 | `.` and `∘` (composition), a name in backticks | right for composition, left for backticks | `f . g` needs a space on each side of the dot (§2.10) |
| 10 | unary `-`, prefix `√` (`sqrt`) | prefix | `-x`, `√x` |
| 9 | `*`/`⊗` `·`/`@` `∧`/`/\` `⊙`/`.*` `⊘`/`./` `/`/`÷` | left | tensor product, contracting product, wedge product, elementwise product and division, division by a scalar (§4.2) |
| 9 | `×`/`><` | none | cross product |
| 8 | `+` `-` `.+` `.-` | left | amounts of one shape (§3.3), point plus amount and point from point (§3.6) |
| 5 | `:` | right | list cons |
| 4 | `==` `/=` `<` `<=` `>` `>=` | none | ordering on `Num` only; equality on any type with equality (§4.2) |
| 3 | `&&` | right | |
| 2 | `\|\|` | right | |
| 1 | `to`, `from … to`, `on` | left, through `to` | conversion and subtraction in a frame (below) |

**Levels in the code.** `Metron.Fixity` defines operator precedence for the
parser and printer. A `#label` labels a complete `sample distribution`
expression. Labels on other expressions are refused.

Level 1 is conversion. `to` converts a display unit, a point or an amount's axes.
`from` names a chart configuration. `b .- a on c` subtracts in frame c.
Conversions associate left: `x to a to b` means `(x to a) to b`.

Products and sums work on amounts of every rank. Named functions include
`dot`, `cross`, `norm`, `transpose`, `inverse`, `det`, `vmap`,
`covariance` and `cholesky`. Component access uses literal projections
such as `v.0` and `m.1.2`.

**Implemented in:** `Fixity`, `Parser`, `Desugar`, `Pretty`.
**Tested by:** "parser", "products", "fixity".

### 2.6 The quantity rule

A number or vector literal followed by one or more atoms is a **quantity**
(§3.10, U4 and U5):

```
quantity ::= number unitatom+
           | vector unitatom+
unitatom ::= atom [ '^' [ '-' ] natural ]
```

- After a literal, declared unit syntax (§3.10, part U) makes the amount
  `scale lit u`.
- After a literal, an expression of chart type makes the point
  `pointOn c lit` (§3.6).
- Anything else is refused: "`pi` is a Num, not a unit or a chart: write the
  `*`".
- Juxtaposed atoms multiply: `9.81 m s^-2` is `9.81 (m*s^-2)`.
- Two literals side by side, `5 4 3` or `2 [1, 2]`, are a parse error. The
  rule exists for units, not arithmetic: `5 * 4 * 3` and `5 * a` are clearer
  written out.
- The whole quantity binds like an application.

**Unit operators bind before numbers** (§3.10, U5). After a literal the
quantity takes the whole unit expression. In a chain of `*` and `/` it takes
in each following factor that is a declared unit's name (§3.2.12: a base unit
or a name declared with `unit`), with or without a power. A number ends it,
and so does any other name. The parser leaves the chain as it is. The
desugarer, which knows which names are declared units, regroups it. Names
decide only the grouping, and the types decide what each operator means.

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

A unit name is syntax, not an ordinary value (§3.10, part U). At an operand
of `*` or `/`, a unit expression means one of that unit: `x * km` is
`x * (1 km)`. Other value positions require an explicit amount (§3.10, U3).
An expression after a coordinate literal that is not declared unit syntax
must be a chart: `\c -> 3 c` infers a chart over a scalar space,
`forall (s : Space (Num d)) (c : s) d. Chart c -> Point c`. Core holds
`scale` or `pointOn`, never the surface quantity rule. Where the spelling
does not decide between them, inference decides and the reading is written
into the term before it is hashed (§4.6, §5.1).

Inside an application there is no such grouping. `f 3 m` applies `f` to `3`
and then to `m`, exactly as `f x y` does, so a quantity in argument position
is parenthesised: `Rect (3 m) (4 m)` and `Body (5 kg) ([1, 2, 3] km)`. The
rule applies only where a literal itself is the head of the expression. A
number applied to something is not a function, and is reported as such:
"Num is not a function and cannot be applied".

**Implemented in:** `Metron.Desugar` (`quantityOf`, `regroup`, `scaleChain`, `unitAmount`, `readingMarker`, `quantityHints`), `Metron.Infer` (`readingsOf`, `rewriteReadings`).
**Tested by:** "units are syntax"; "internal units and public amount arithmetic"; "amount arithmetic"; "units".

### 2.7 Grammar

The grammar is over canonical tokens, after the unicode mapping of §2.8.

```
program    ::= statement ( sep statement )*
sep        ::= newline-at-column-0 | ';'
statement  ::= 'let' name param* '=' expr [ 'where' bindings ]
             | 'unit' name '=' expr                      -- a display unit (3.2.12, 3.10 U7)
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
binder     ::= name | '(' name ':' natural ')' | '(' name ':' qname ')' | '(' name ':' type ')'
                                                       -- a variable; one sized: that many axes of its own (3.9);
                                                       -- a frame of a space (3.10 F1); a constrained space, (s : Space (Vec 3 m))
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
               with `name` and composition at level 11 and
               '#'label as a postfix at level 6 (3.2.4)
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

**Implemented in:** `Metron.Parser` (`program`, `statement`, `chartStatement`, `clauseSegments`, `expr`, `opExpr`, `application`, `atom`, `primary`, `patternP`, `sigType`, `typeExpr`).
**Tested by:** "parser"; "forall"; "dimension syntax".

### 2.8 Unicode spellings

The lexer maps unicode to canonical tokens. Every construct has an ASCII
spelling, so a plain keyboard is never a barrier, and the pretty-printer can
emit either.

| Unicode | ASCII | Meaning |
|---|---|---|
| `λ` | `\` | lambda |
| `→` | `->` | arrow |
| `·` `⋅` | `@` | contracting product: dot, matrix-vector, matrix-matrix; name `dot`. In a dimension (§4.1) `·` is `*`, the product, and `@` is refused |
| `⊗` | `*` | tensor product; name `outer` |
| `×` | `><` | cross product; name `cross` |
| `⊙` | `.*` | elementwise product; name `emul` |
| `⊘` | `./` | elementwise division; name `ediv` |
| `÷` | `/` | division by a scalar; name `div` |
| `≤` `≥` `≠` | `<=` `>=` `/=` | comparison |
| `∨` `¬` | `\|\|` `not` | boolean or and not. Boolean and is `&&` only, because `∧` is the wedge product |
| `∧` | `/\` | wedge (exterior) product; name `wedge` |
| `⋆` | `star` | 3D Hodge star, prefix; name `star` |
| `°C` `°F` | `degC` `degF` | temperature charts (§3.6). `°` alone is `deg` |
| `√` | `sqrt` | prefix: `√x`, `√(a² + b²)` |
| `∘` | `.` | composition |
| `∀` | `forall` | binds a signature's or an ascription's type variables (§4.8). Input only, printed `forall` |
| `²` `³` `⁻¹` … | `^2` `^3` `^-1` | superscript digits and `⁻` as a power: `m/s²`, `s⁻²` |
| `π` | `pi` | the constant |
| `°` | `deg` | postfix unit: `45°` is `45 deg` |
| `″` `′` | `arcsec` `arcmin` | postfix units |
| `₀` `₁` … | `_0` `_1` … | subscripts inside identifiers only |

Rules:

- Superscripts bind as `^` does, so `3 m²` is `3 (m^2)` by the quantity rule.
- A superscript is a power only when it follows an atom with no space
  between. `x ²` is refused: "a superscript power must be attached to the
  thing it raises, as in m² or x⁻¹".
- `°` and the arc marks attach to the preceding number with no space and are
  unit atoms, so `45° + 30′` works.
- Inside an identifier, `_` followed by digits is those digits as
  subscripts: `v_0` is the identifier `v₀`, and `x_12` is `x₁₂`. The first
  character is the identifier's own, so `_0` stays `_0`. A name given to a
  command folds the same way. Names print in their unicode spelling.

The printer emits ASCII by default. `:set unicode on` (§7.3) switches the
exponents, `->`, `\` and `<= >= /= ||` to their unicode spellings. §7.3 has
the exact set for output, and the echo, which re-spells each statement line
as typed.

In the REPL a character can be typed by name, as in Julia: `\mu` then TAB
becomes `μ`, `\^2` becomes `²`. §7.3 has the table. Every
entry lexes as its ASCII spelling here, or is an identifier letter.

**Implemented in:** `Metron.Lexer` (`symbol`, `superscript`, `isSuperscriptDigit`, `subscripted`, `prepare`), `Metron.Session.Names` (`argPaths`), `Metron.Unicode` (`completions`, `lookupName`), `Metron.Pretty` (`respell`).
**Tested by:** "lexer"; "unicode echo"; "repl".

### 2.9 Desugaring

Everything in this table is removed before Core. The right column is Core
written in surface notation.

| Surface | Core |
|---|---|
| `let f x y = e` | `let f = \x -> \y -> e` |
| `\x y -> e` | `\x -> \y -> e` |
| `let f x = e where k = …` | `let f = \x -> let k = … in e`. Where-bindings are non-recursive and scope over `e` |
| ``a `g` b`` | `g a b` |
| `(+ 1)`, `(2 *)` | `\x -> x + 1`, `\x -> 2 * x` |
| `vmap sqrt v`, `foldr add 0 xs` | `vmap (\x -> sqrt x) v`, …: a primitive used as a value is eta-expanded to its arity, because Core primitives are saturated (§5.1). The binders of such a lambda carry a hint no identifier spells (`Metron.Core.etaHint`), and the pretty-printer eta-reduces these for display: `let h = vmap sqrt` views as `h = vmap sqrt`. A lambda the user wrote stays one, `\x -> neg x` views as `\x -> -x`, and so does one applied, since `sqrt 4` would read back as another term. Hints are not hashed, so both read back to the same hash |
| `f ∘ g` | `\x -> f (g x)` |
| `3 m²`, `3 m s⁻²` | `scale 3 (m^2)`, `scale 3 (m*s^-2)` (the quantity rule, §2.6) |
| `20 degC` | `pointOn degC 20` |
| `45°` | `scale 45 deg` |
| `√e` | `sqrt e` |
| `a + b`, `a * b`, `a · b`, … | `add a b`, `outer a b`, `dot a b`, …: every operator is a saturated application of the primitive of the same name, and the names work prefix and in backticks |
| `v.2` | `Proj v 2` (a node with a literal position, §5.1) |
| `m.1.2` | `Proj (Proj m 1) 2` |
| `m._.0`, `t._._.2`, `t._.0.1` | `slice 1 0 m`, `slice 2 2 t`, `Proj (slice 1 0 t) 1`: the primitive applied to the axis (the number of wildcards) and the position as constants (§2.10), whatever `slice` names in scope |
| `a to u` | `to a u` for a unit, keeping `u`'s term as the display hint. For a chart, `toChart` or `toAxes`, chosen by the types (§3.10, U6, F10) |
| `p from c to c1` | `fromTo p c c1` for a point, `axesFromTo` for an amount (§3.10, F7) |
| `b .- a on c` | `let x = c in (b to x) .- (a to x)` (§3.10, F10) |
| `-x` | `neg x`. But `-3`, or `-` applied to any constant tensor, is the negative constant itself, so a negative literal has one nominal form |
| `if c then a else b` | `case c of False -> b; True -> a`, lazy in both branches (§5.1) |
| `[a, b, c]` | `Pack [a, b, c]`. A bracket whose elements are all constants is one `Lit` |
| `x ^ n` | `Pow x n`, `n` an integer literal |
| `contract i j t`, `permute [p…] t`, `slice k i t` | the primitive applied to its literal positions as constants and then `t` (§4.2). The desugarer checks that the positions are literal naturals, distinct for `contract`, and a permutation of `0 .. k-1` for `permute`. A bare `contract`, `permute` or `slice` is refused. Leaving off only `t` eta-expands, as for any primitive |
| `b.f`, `C {f = e}`, `b {f = e}` | `case` on the record's one constructor (§2.3) |
| `1_000_000`, `9.81`, `1e-3` | the exact rational |
| a free name `x` | `Ref #hash` of what `x` points at when the definition is entered, with the written name kept for storage (§6.1) |

Desugaring is total and local. No step consults the codebase except
name-to-reference resolution, and no step needs type information except the
readings of the quantity rule and of `to`, which the desugarer leaves as
markers for inference to resolve (§2.6). The refusals quote the rule:

- "contract pairs two different positions, not position 0 with itself:
  contract i j t, with i and j distinct".
- "contract takes two literal positions and then a tensor: contract i j t,
  with i and j distinct natural numbers".
- "permute [0, 0] is not a permutation of 0 .. 1: each position from 0 to 1
  must appear exactly once".

**Implemented in:** `Metron.Desugar` (`desugar`, `eta`, `saturated`, `opPrim`, `specialForm`, `indexedForm`, `primLiterals`, `foldConstant`, `caseOf`, `recordExpr`, `quantityOf`), `Metron.Core` (`etaHint`, `strengthen`), `Metron.Primitive` (`primArity`), `Metron.Pretty` (`renderTerm`, `renderTermUnits`).
**Tested by:** "desugar"; "contraction and permutation"; "slicing along an axis"; "pretty".

### 2.10 Component access and qualified names

Vectors and matrices are indexed by **literal position only**, with a
postfix dot:

```
v.0   v.1   v.2        -- components of a vector
m.1                    -- row 1 of a matrix, a vector
m.1.2                  -- row 1, column 2
m._.0                  -- column 0 of a matrix: any row, position 0 of the next axis
t._._.2                -- position 2 of the third axis of a rank-3 tensor
```

- A projection peels the first axis.
- To pick a position along a later axis, write one wildcard `._` for each
  axis to skip, then the position. `m._.0` is column 0, the same vector as
  `(transpose m).0`, and `t._._.2` drops the third axis of `t` at position 2.
- Each wildcard skips exactly one axis, and the chain reads left to right as
  `m.1.2` does. So `t._.0.1` slices axis 1 at 0 and then projects the first
  axis of the result at 1: `(slice 1 0 t).1`.
- The wildcard form is sugar for the primitive `slice k i t` (§3.3), with `k`
  the number of wildcards. `slice` can also be written out, with the same
  literal rules as `contract`. `slice 0 i t` is the same tensor as `t.i`, but
  a different term: `t.i` stays a projection.
- A wildcard must be followed by a position. `m._` alone is a parse error: "a
  wildcard ._ skips an axis and must be followed by a position, as in m._.0
  for column 0".
- Slices apply to tensors, not to points (§3.6). A projection applies to
  both.
- `:view` prints a slice along axis `k ≥ 1` back with wildcards
  (`col = \t -> t._.0`) and `slice 0 i t` by name, so both re-parse to the
  same term. `:core` prints the primitive form.
- A position out of range is a type error (§4.1): `[1, 2].2` is "position 2
  is out of range for a vector of length 2", `[1, 2; 3, 4]._.2` is "position
  2 is out of range for axis 1 of length 2", and `[1, 2, 3]._.0` is "slice 1 0
  needs a tensor of rank at least 2, got Vec 3".

There is no `index v i` with a computed `i`. The position is part of the type
(§4.1), so an out-of-range access is a compile-time error, and
`let first v = v.0` is a polymorphic function that takes any tensor whose
first length is at least one. Iteration over components uses `vmap`, `dot`,
`norm` and the others, never a loop over indices. Where a computation needs
a component's position, `indices v` (and the library's `vimap`, §3.3) gives
the positions as values, `[0, 1, …, n-1]`, and `timap` gives each component
of a tensor of any rank its multi-index as a vector. This adds no computed
indexing, because no primitive takes such a value as a position.

**Open.** Letter names for positions (`.x .y .z`, `.pos .vel`) are a planned
sugar at the desugaring layer, designed as §3.9's layer 1 and not built
(§10).

**Lexing.** The dot must follow the atom immediately and be followed
immediately by digits, or by a name for a record field (§2.3):

- `v .0` is refused: "a projection like .0 must be attached to a vector or
  matrix, as in v.0". `v. 0` is an error too.
- `1.5` is a number, because the lexer reads numbers before it looks for
  projections. A projection or field can only follow a name, a parenthesised
  expression, a literal or another projection.
- A dot with a space on each side (`f . g`) is composition, as is `∘`. `f.g`
  is the field `g` of `f`.
- A wildcard is a dot glued to the atom (or to the projection or wildcard
  before it), followed by `_`, where the `_` does not start an identifier.
  Digits or another wildcard follow, glued: `m._.0`, `t._._.2`. `m ._.0` is
  an error, and `x._y` is the composition of `x` and the name `_y`.

**Qualified and absolute names** (§7.6). A dot and a name that are *not*
glued to an atom start an absolute name. `.km` is the root's `km`, whatever
namespace is current or used, and `.orbital.period` is the full path from
the root. So `f .g` is `f` applied to the root's `g`.

A glued chain on a name, `orbital.period` or `o.period`, lexes as field
accesses, and the desugarer decides what it is:

- When the name at its head is a local binder, the chain is field access:
  `b.mass` with `b` a lambda parameter is a field access whatever labels
  exist.
- Otherwise the longest dotted prefix of the chain that resolves (§7.6) to a
  definition or a constructor is a qualified reference, and the names after
  it are field accesses. `orbital.earth.mass` is the field `mass` of the
  definition `orbital.earth`.
- A field written after the dot is a bare name and resolves through the scope
  only. So `orbital.earth.mass` needs the field `mass` in scope, for example
  through `use orbital`. Otherwise it is "unknown field `mass`".
- A record built with a constructor, `orbital.Body {mass = …}`, takes the
  field names as that constructor's own, wherever the type lives.
- The one ambiguous case, a value `orbital` with a field `period` beside a
  definition `orbital.period`, cannot arise, because a name is never both a
  label and a namespace (§7.6).

**Implemented in:** `Metron.Lexer` (`projection`, `wildcard`, `field`), `Metron.Parser` (`atom`, `primary`), `Metron.Desugar` (`qualifiedChain`, `indexedForm`, `fieldVar`), `Metron.NameResolution` (`resolverFor`, `qualifyName`).
**Tested by:** "slicing along an axis"; "namespaces" › "an absolute .name picks the root's"; "namespaces" › "lexing: a dot not glued to a value is an absolute name"; "data".

## 3. Values, numbers and units

### 3.1 The value universe

| Static type | Runtime value | Notes |
|---|---|---|
| `Num δ` | a magnitude (§3.2) plus a dimension vector and a display-unit hint | `δ` is checked statically. The runtime dimension vector exists for printing only. `Num δ` is the rank-zero tensor `Tensor [] δ` (§3.3) |
| `Bool` | `true` or `false`: constructor `False` or `True`, with no fields | `structural data Bool = False \| True` (§2.3). `if` is `case` on it |
| `(a, b, …)` | a tuple of values: the one constructor, its fields as thunks | the structural tuple type of its arity, `Pair a b` for two. Components have any types, so a state `(r, v)` has two dimensions |
| `{a}` | a list: `{}` or `x : xs`, constructor `Nil` or `Cons` | `structural data List a`. The one unbounded structure. It is lazy, so `range` and `map` stream |
| `T α…` (declared, §2.3) | a constructor and its fields, as thunks | `Shape`, `Maybe (Num m)`, `Tree a`. `Bool`, tuples and lists are three of them |
| `a -> b` | a closure: a term plus its environment | first class, and hashed like everything else |
| `Tensor s δ` | a flat row-major buffer of magnitudes, its shape `s`, one shared dimension vector and hint | `s` is a type-level list of lengths. `Vec n δ` and `Mat m n δ` are how `Tensor [n] δ` and `Tensor [m, n] δ` print. Rotations are `Mat 3 3 1` |
| `Point c`, `Chart c` | a point's coordinates and chart, or a chart value | §3.6, §3.8 and §3.10 |

There is no unit type `()`, because there are no effects. There are no
strings, because nothing consumes them. There is no `Int` separate from
`Num`. An integer is an exact rational with denominator 1. The positions
that need an integer (the exponent of `^` and tensor indices) are syntactic restrictions, not types.

Declared types are the data types, and `case` (§2.3) consumes them. `Bool`,
tuples and lists are declared types that the compiler holds (§2.3). They
differ from the others only in having syntax of their own. At run time a
boolean is a constructor with no fields, like any other.

**Implemented in:** `Metron.Eval` (`ValueOf`, `evalClosed`), `Metron.Builtin` (`boolDef`, `pairDef`, `listDef`, `tupleDef`).
**Tested by:** "evaluation"; "data".

### 3.2 Arithmetic and sampled inputs

**Decided.** Arithmetic and uncertainty propagation are separate. Choose rational
or IEEE double arithmetic. Describe uncertain inputs with explicit distributions.
Monte Carlo propagation evaluates the expression for each input realization.
It does not certify a numerical error bound.

#### 3.2.1 Rational operations

Rational addition, subtraction, multiplication, division and integer powers
operate exactly on represented operands. Division by zero fails explicitly.
The digits limit refuses excessive rational growth rather than rounding it silently.

#### 3.2.2 Double operations

Double arithmetic follows IEEE nearest rounding in the ordinary evaluation.
NaN, infinity and underflow remain visible. Optional stochastic rounding runs
are separate diagnostics (§8.2), not replacements for the ordinary result.

#### 3.2.3 Where approximation enters

Irrational constants, elementary functions and normal random variates require
approximation. Rational arithmetic uses precision-controlled rational kernels,
without silently converting to doubles. Internal approximation intervals serve
those kernels only. The final value carries no guaranteed enclosure.

#### 3.2.4 Sample identity is content-addressed

A Core `Sample label distribution` has a lexical source identity. An explicit
`#label` names a shared source. Otherwise the declaration owner and Core path
identify it. Two sample sites are independent. Reusing a sampled value reuses
the same realization, including through closures, storage and chart conversions.
Repeated calls to one lexical sample site reuse its latent draw. To request
independent inputs, use distinct sample sites.

Rounding identities are separate: they include the operation site, application
path, component and internal operation index. Input index and rounding repetition
index select separate random streams. Branches do not advance a global generator.

#### 3.2.5 Distributions and sampling

```text
let length = sample (normal (2 m) (0.01 m))
let width = sample (uniform (0.995 m) (1.005 m))
let area = length * width
```

`normal mean sd` and `uniform lower upper` produce `Distribution d`.
Their scalar parameters must have matching dimensions and must be deterministic.
Standard deviation must be nonnegative. Uniform endpoints must be ordered.
A zero-width distribution is valid. The parameter expressions and distribution
generation are excluded from stochastic rounding analysis.

Uniform inputs use rational midpoint cells from deterministic 64-bit random words.
Normal inputs use rational Box–Muller calculations at the configured precision.
The finite generator approximates the requested distribution.

#### 3.2.6 Statistical summaries

`mid x` is the empirical mean of ordinary input results.
`sd x` is their sample standard deviation, with denominator N−1.
They require sampled inputs. Sample deviation and covariance require N≥2.
They reject stochastic rounding analysis of reductions until that model is specified.
These names do not extract an exact center or a guaranteed error.

#### 3.2.7 Storage and limits

Each scalar carries ordinary arithmetic and, where needed, its indexed realizations.
There is no affine coefficient map, slack, compaction or hard-bound representation.
The combined run count is checked before allocation. Memory, time, digits, depth
and component limits still apply. See §8.1 and §8.2.

#### 3.2.8 Working precision

`:set precision P` controls rational approximations and decimal display.
It does not increase double precision or the accuracy of input measurements.
Exact rational operations do not shorten their operands automatically.
Matrix exponential kernels shorten intermediate rational approximations to control cost.

#### 3.2.9 Comparison

Each realization follows its own comparisons and branches. Shared values cancel
within each realization. Double comparisons follow IEEE rules, including NaN.
Different constructors produce a mixture of outcomes rather than an undecidable
comparison caused by overlapping error bounds.

#### 3.2.10 Printing

Print the ordinary value first. Input reports show empirical mean, sample standard
deviation and the central 95% outcome interval, with the input count.
Quantiles use linear interpolation at (N−1)p (type 7).
Rounding reports show within-input spread and displacement from ordinary results.
Neither report is a confidence interval for the mean or a guaranteed bound.
Nonfinite results and unsupported conditional summaries are explicit.

**Implemented in:** `Rational`, `Double`, `Scalar`, `Numerical.Rational`,
`Numerical.Sampling`, `Numerical.Statistics`, `Eval`, `Pretty`.
**Tested by:** "separate sampling foundation", "independent arithmetic and grouped rounding",
"rational approximation kernels", "numerical review regressions".

#### 3.2.11 Units and dimensions at runtime

The base dimensions are the seven of the SI, length L, mass M, time T,
current I, temperature Θ, amount N and luminous intensity J, **plus plane
angle**, whose base unit is the radian. Their base units
`m kg s A K mol cd rad` are **built-ins** of dimension L, M and so on,
written `Num m`, `Num kg`, … in types (§4.1). They are units (§3.10, U1),
not names: they need no namespace, cannot be renamed, and are available
everywhere.

**Decided.** The SI declares the radian dimensionless, so that `s = r θ`
and `sin θ` read as the formulas are written. Metron gives angle a
dimension instead, as Boost.Units does, because the calculator's job is
to catch the mistakes the formulas invite:

- `sin 1` is an error that asks for `1 rad` or `45 deg`: "sin takes an
  angle: write 1 rad or 45 deg".
- angular velocity `rad/s` and frequency `Hz` are different types, and
  cannot be added or confused by a factor of 2π.
- `sr = rad^2` makes the photometric units honest.

The price is that an angle must be divided out where the SI quietly drops
it. Arc length is `r * θ / 1 rad`, and angular velocity from a speed is
`v / r * 1 rad`. This is the same bookkeeping every other dimension asks
for.

Every other unit is library source written in the language, and therefore
hashed, viewable and rebindable (§7.7 has the layout):

```
unit N  = kg*m/s^2              -- a unit from a unit
unit J  = N*m
unit km = kilo * 1 metre        -- a unit from an amount, its size
unit g  = 1 kg / 1000           -- the one wrinkle: the base unit carries a prefix
unit deg = pi / 180 * 1 rad
```

So `90 deg` prints as itself, and `sin (90 deg)` is
`1.0000000000000000000…`. The library ships the 22 derived SI units, the
24 prefixes applied to every base and derived unit, and the accepted units
iapetus needs. `Metron.Prelude` generates the prefix table.

**Decided.** Measured constants use explicit normal distributions with the
published mean and standard uncertainty. For example,
`astro.G = sample (normal 6.67430e-11 1.5e-15) * 1 m^3/kg/s^2`.
Derived quantities share their sampled constants. SI defining constants,
IAU nominal values and WGS84 defining parameters remain deterministic.

The run-time errors are listed in §4.7. Everything else, including a
component access out of range, is caught statically.

**Implemented in:** `Metron.Dimension` (`BaseDim`, `baseSymbol`), `Metron.Primitive` (`baseUnit`), `Metron.Prelude` (`stdlibSource`, `prefixNames`, `coherent`).
**Tested by:** "units" › "base units are primitives"; "units" › "the circular functions take an angle"; "prelude" › "derived units are coherent"; "prelude" › "accepted units"; "prelude" › "constants are exact where SI defines them so"; "separate sampling foundation"; "astro (design §7.7)".

#### 3.2.12 Display units

Magnitudes are always stored in SI base units. Values print in base units
factored (`m s^-2`) unless they carry a *display unit*: a product of named
units with exponents, a scale factor and a dimension.

**Where display units come from.**

- A definition declared with `unit` instead of `let` is a display unit:
  `unit km = 1000 m`. Its term is a unit (§3.10, U7): the declaration
  makes its body, an amount or a unit, a unit. So `unit dozen = 12` and
  `let eggs = 12` are two terms. That a unit is its own display unit is a
  property of the **name**, label-level metadata in the codebase like the
  binding itself, and not part of the hash. `Bq` and `Hz` are one term,
  `s^-1`, yet each prints as written. This works because every reference
  in Core carries the name the author wrote as a hint, ignored by the hash
  like a binder's name but kept in the store, and the evaluator asks
  whether *that* name is a unit.
- A `let` that rebinds a unit name (`let g = 9.81 m/s^2`) makes it a
  quantity. `:alias` of a unit makes the alias a unit. `:unname` removes
  the flag. If the written name has since been moved or removed, any
  current unit name of the same reference stands in, so a renamed unit
  prints under its new name.
- Evaluating a reference to a declared unit yields its value tagged with
  itself, so `5 km` prints `5 km` and `1 km to m` prints `1000 m`. The
  seven base units are units by construction. A `let`-bound quantity is
  not a unit: `let g = 9.81 m / s^2` prints as `9.81 m s^-2`, and so do
  values computed from it.

**How operations combine them.**

- `*`, `·`, `⊙`, `∧` and `^` combine display units by multiplying them.
  `/` and `⊘` divide. `5 km / h` prints `5 km h^-1`, and `(2 km)^2` prints
  `4 km^2`. Unit names keep the order they were written in, so `1 V * 1 A`
  prints `1 V A`.
- Units of one dimension that meet with opposite signs cancel, with their
  factor folded into the number: `2 m * 90 deg / rad` is
  `3.1415926535897932384… m`, `3 h / min` is `180`, and `(2 km)^2 / 1 m`
  is `4000 km`. After a literal the quantity takes in the units that
  follow it (§2.6), so `90 deg / rad` is `90 (deg/rad)`, whose units
  cancel when the quantity is taken. Unit arithmetic itself cancels
  nothing: the unit `km/m` prints as `km/m` (§3.10, U8).
- `+` and `-` take the **smaller** of their operands' units, so that the
  result does not depend on operand order: `5 km + 3 m` and `3 m + 5 km`
  are both `5003 m`.
- Projection, packing, negation, `abs`, `norm`, `transpose` and `⋆` keep
  the unit. Every other operation drops it.
- `x to u` replaces the display unit with `u`'s. `u` is a unit (§3.10,
  U6), as in `x to km/h`, never an amount. `to` is shape-polymorphic.
  `:prefer` takes a unit too.

**Which unit a result prints in**, in order:

1. An explicit `to` wins.
2. Otherwise a declared **preference** for the value's exact dimension:
   `:prefer km/h` makes every velocity print in km/h until
   `:unprefer km/h`. There is one preference per dimension, kept in the
   codebase and so across sessions.
3. Otherwise the written units, carried and simplified as above:
   dimensionless results are plain numbers, units of one dimension
   cancel, and sums take the smaller unit.
4. Otherwise, when an operation drops the hint, SI base units.

**Decided.** There is no best unit for a result, only the one the user
wrote or asked for, so the rule never invents one. `1 V * 1 A` prints
`1 V A`, not `1 W`, because `N m` is as often a torque as a joule. A
display unit whose dimension does not match the value's is ignored and
base units are printed, so the rule can never show a wrong number. Units
print by their current name through the same resolution as `:view`
(§7.6).

**Implemented in:** `Metron.UnitHint` (`UnitHint`, `mkHint`, `hintMul`, `unitHintMul`, `unitHintDiv`, `unitHintPow`, `smallerUnit`, `combine`, `hintProduct`), `Metron.Session.Preferences` (`preferenceHint`, `refreshPreferences`), `Metron.Eval` (`asUnit`), `Metron.Pretty` (`renderValue`).
**Tested by:** "units"; "display units"; "spaces and frames (design §3.10, part F)"; "turnedCharts"; "movingCharts"; "standard library".

### 3.3 Vectors, matrices and tensors

**Open.** A proposed common indexed amount type extends tensors with
exterior powers while preserving distinct products and explicit Core.
See [Indexed amounts and exterior algebra](indexed-amount-proposal.md) for
grade-zero/grade-one normalisation, inference limits and implementation
scope. This is not adopted; the rules below describe the current design.

There is one aggregate type, `Tensor s δ`. The shape `s` is a type-level
list of lengths (§4.1). A number is a rank-zero tensor, a vector has rank
one, a matrix rank two, and higher ranks (an inertia tensor's gradient)
come for free. `Num`, `Vec n` and `Mat m n` are the printer's names for
ranks zero, one and two. A literal `[a, b, c]` stacks three tensors of
shape `s` into one of shape `3 : s`, so `[[1, 2], [3, 4]]` is a vector of
vectors. Projection `t.i` peels one length off the front of the shape. It
gives a number from a vector and a row from a matrix by the same rule.

**Decided.** Rank-polymorphic contraction (`einsum`) is out of scope.
Every primitive has a fixed-rank signature, or is polymorphic in the whole
shape, or (`contract`, `permute`, `slice`) has a signature computed from
literal index positions written at the call, as a projection's position
is. So unification stays first-order.

**The empty literal.** `[]` is a tensor of length zero whose element type
comes from context, as any literal's does: an ascription
(`([] :: Vec 0 m)`, `([] :: Mat 0 3 m)`), unification with another operand
(`dot ([] :: Vec 0 m) ([] :: Vec 0 m)` is `0 m^2`), or a signature. Typed
Core keeps a pack's element type even with no elements (`TPack`), and an
empty pack is built from it (§8). A definition can leave it open:
`let e = []` is `forall s d. Tensor (0 : s) d`, and each use chooses. An
expression at the prompt whose value leaves open, outside any function, a
length, shape or dimension that building it needs has no value to build.
It is refused as a type error: "ambiguous: nothing fixes the shape or
dimension of this value, of type Tensor (0 : s) d; give an empty tensor a
type, as in ([] :: Vec 0 m)". (`Empty` of `data Box d = Empty | Full
(Num d)` needs none, and is built.)

**Size.** Lengths, counts and index positions are machine integers. A
length a type or a literal names is at most `2^40` (`lengthLimit`), so
that a definition checks the same in every session. One written past it
(`Vec 18446744073709551616` in a signature,
a projection `.18446744073709551616`, a position of `contract` or
`slice`) is refused where it is written, never wrapped: "a tensor has at most 2^40 components". How many
components a tensor can have when it is built is the session's
`components` limit, default 10⁷ (§8.1). A product whose operands are
within it but whose result is not (`outer`, `dot`, `wedge`) is refused
when it runs: "the result would have 16000000 components, more than
10000000 (`:set components`)".

**Decided.** Tensors are **homogeneous**: all components share one
dimension. A position is `Vec 3 m`, a velocity `Vec 3 (m/s)`, a rotation
`Mat 3 3 1`. A six-element state is the tuple `(r, v)`, not a `Vec 6`. Its
covariance and state-transition matrix, whose entries mix dimensions, are
written as homogeneous blocks (§3.7).

Each component carries indexed realizations. Shared sources preserve correlation
across components through the complete calculation (§3.4).

**Operators**, each with one type (§4.2):

| Operator | Name | Meaning | Dimension rule |
|---|---|---|---|
| `+`, `-` | `add`, `sub` | elementwise on tensors of one shape | same `δ` |
| `*`, `⊗` | `outer` | tensor product: ranks add. Scalar scaling is the rank-zero case | `δ₁·δ₂` |
| `·`, `@` | `dot` | contracting product: the last index of the left with the first of the right. Dot product, Mat·Vec, Mat·Mat | `δ₁·δ₂` |
| `∧`, `/\` | `wedge` | wedge product: the oriented plane of two vectors, any dimension | `δ₁·δ₂` |
| `⋆` | `star` | 3D Hodge star: a bivector to its normal vector | same `δ` |
| `×`, `><` | `cross` | 3D cross product, mathematically `(ε @ b) @ a`. There is no binary cross product in other dimensions. The general tool is contraction with the Levi-Civita tensor `ε`: `a × b = (ε · b) · a` | `δ₁·δ₂` |
| `⊙`, `.*` | `emul` | elementwise product | `δ₁·δ₂` |
| `⊘`, `./` | `ediv` | elementwise division | `δ₁/δ₂` |
| `/` | `div` | division by a scalar | `δ₁/δ₂` |
| `==`, `/=` | `eq`, `ne` | on tensors of one shape, points and data (§4.2): the one overloaded primitive | same type |
| `to` | `to` | display unit on any tensor (§3.2.12) | same `δ` |

**Decided.** `star` is the Euclidean 3D Hodge star on alternating
matrices, with the standard orientation. It verifies diagonal zeros and
`M + transpose M == 0`, including every double copy. Non-alternating or
undecidable inputs are refused. To project a general matrix, write
`star ((M - transpose M)/2)` explicitly. The wedge computes one triangle and negates it for the other.
Identical finite operands produce a zero wedge in ordinary arithmetic.
Under diagnostic rounding, arithmetic identities are subject to the perturbation model.
General exterior grades, metric and orientation remain future work; this
matrix boundary is not a general Grassmann representation.

`cross a b` computes `contract 1 2 (ε @ (a ∧ b))/(-2)`. Its final
`vzipWith (\_ z -> z) a` ties the output axes to the input axes in the
type system; it does not change the coefficients. This contraction is
known alternating by construction, so statistical vectors do not need a
runtime `star` comparison that discarded remainders cannot prove.
`vzipWith` retains the first input's display unit whose dimension matches
the output, falling back to the second input's. This also preserves the
cross product's compound unit through its shape-preserving projection.

**Named functions:**

```
dot        : Vec n d1 -> Vec n d2 -> Num (d1*d2)
cross      : Vec 3 d1 -> Vec 3 d2 -> Vec 3 (d1*d2)       -- linalg
norm       : Vec n d -> Num d
transpose  : Mat m n d -> Mat n m d
inverse    : Mat n n d -> Mat n n (1/d)
det        : Mat n n 1 -> Num 1              -- any n, dimensionless only (§4.6)
vmap       : (Num d1 -> Num d2) -> Tensor s d1 -> Tensor s d2
vzipWith   : (Num d1 -> Num d2 -> Num d3) -> Tensor s d1 -> Tensor s d2 -> Tensor s d3
indices    : Vec n d -> Vec n                -- [0, 1, …, n-1], exact; positions as values
vimap      : (Num -> Num d1 -> Num d2) -> Vec n d1 -> Vec n d2
                                             -- linalg: vimap f v = vzipWith f (indices v) v
timap      : (Vec (rank s) -> Num d1 -> Num d2) -> Tensor s d1 -> Tensor s d2
                                             -- the multi-index as an exact vector, any rank (§4.1)
v.i        : Vec (n + i + 1) d -> Num d      -- projection, i a literal (§2.10, §4.1)
m.i        : Mat (k + i + 1) n d -> Vec n d  -- row projection
covariance : Vec n d -> Mat n n (d^2)        -- §3.5
crossCovariance : Vec n d1 -> Vec m d2 -> Mat n m (d1*d2)   -- §3.5
cholesky   : Mat n n (d^2) -> Mat n n d      -- §3.5
contract i j : Tensor (l0 : … : lj : s) d -> Tensor (… without i and j : s) d
                                             -- i ≠ j literals, li = lj; a trace (§4.2)
permute [p0, …, pk-1] : Tensor (l0 : … : lk-1 : s) d -> Tensor (lp0 : … : lpk-1 : s) d
                                             -- the p a literal permutation of 0 .. k-1
slice k i  : Tensor (l0 : … : lk-1 : n + i + 1 : s) d -> Tensor (l0 : … : lk-1 : s) d
                                             -- k, i literals; written t._.i with k wildcards (§2.10)
trace      : Tensor (n : n : s) d -> Tensor s d   -- linalg: trace a = contract 0 1 a
expm       : Mat n n -> Mat n n              -- the matrix exponential, dimensionless; a rotation from a bivector
transformBy : Mat n n -> Tensor s d -> Tensor s d   -- R along every axis; every length must be n; anonymous axes only (§3.9)
seq        : a -> b -> b                     -- b, once a is evaluated (§7.7)
e1 e2 e3   : Vec 3                           -- linalg: the unit vectors
rotx roty rotz : Num rad -> Mat a a          -- linalg: the bivector of a turn about an axis, right-handed, over any one three-axis set (§3.9)
dual       : Tensor (3 : s) d -> Tensor (3 : 3 : s) d   -- linalg: dual v = ε @ v, the inverse of ⋆
axisAngle  : Vec 3 d -> Num rad -> Mat 3 3   -- linalg: the bivector of a turn about any axis
rotation   : Vec 3 d -> Vec 3 d1 -> Mat 3 3  -- linalg: the bivector taking a's direction to b's
euler313   : Num rad -> Num rad -> Num rad -> Mat a a   -- linalg: the 3-1-3 matrix, over one three-axis set
rotateVec  : Mat n m d -> Tensor (m : s) d1 -> Tensor (n : s) (d*d1)   -- linalg: r v, typed by r's rows and columns (§3.9)
rotateCov  : Mat n m d -> Mat m m d1 -> Mat n n (d^2*d1)               -- linalg: r p rᵀ, a covariance turned (§3.9)
```

The chart functions (`rotationOf`, `spinOf`, `originOf`,
`originVelocityOf`, `withAxes`, `v to c`, `v from c to c1`) are in §3.8
and §3.10.

**Rotations.** A rotation is generated by a *bivector*: an antisymmetric
`Mat n n`, the oriented plane of the turn with the angle as its size.
`expm` makes the rotation matrix from it. The constructors in `linalg`
build bivectors, and `expm` and `@` turn them into matrices and compose
them:

```
> expm (rotz (90 deg)) @ [1, 0, 0]
[1.6412796919477191898…e-27, 1.0000000000000000000…, 0]
> rotz (30 deg) == axisAngle [0, 0, 1] (30 deg)
true
> rotation e1 e2 == rotz (90 deg)
true
> transformBy [[0, -1, 0], [1, 0, 0], [0, 0, 1]] [[4, 1, 0], [1, 9, 0], [0, 0, 1]]
[9, -1, 0; -1, 4, 0; 0, 0, 1]
> :type rotation
forall d d1 (a : 3) (b : 3). Vec 3 d -> Vec 3 d1 -> Mat a b
```

The bivector's axes are free, `(a : 3)` and `(b : 3)`, because `dual`'s
`ε` is a literal, and a literal takes its axes from use (§3.9, decision
5). Its arguments are anonymous because `rotation` names a local value
built from `e1` and `e3`, and a named value's default makes that
anonymous.

- `a ∧ b` is the matrix `a bᵀ − b aᵀ`, whose product with a vector turns
  `b` toward `a`: `(e1 ∧ e2) @ e1` is `[0, -1, 0]`. So the generator of
  the turn from `a` toward `b` is `b ∧ a`, and `rotz θ = θ (e2 ∧ e1)`,
  `rotx θ = θ (e3 ∧ e2)`, `roty θ = θ (e1 ∧ e3)`, each with the angle
  divided by `1 rad`. The constructors write `(θ to rad) / 1 rad`, which
  fixes the argument to an angle. `expm (rotz (90 deg))` turns `e1` to
  `e2`: the right-hand rule. `⋆` keeps its sign (`⋆ (e1 ∧ e2)` is `e3`, so
  `cross` is the usual one), and so `⋆ (rotz θ) = −θ e3`.
- `dual v = ε @ v` is the inverse of `⋆` on bivectors (`⋆ (dual v) = v`,
  `dual v @ u = u × v`), and `b ∧ a = dual (b × a)`. `axisAngle n θ`, the
  turn by `θ` about `n` by the right-hand rule, is the dual of
  `−θ n / norm n`, and `axisAngle [0, 0, 1] θ == rotz θ`. `dual` is not
  the generator about `v`. That is `dual (−v)`, the matrix of `u ↦ v × u`.
- `rotation a b` is the bivector of the smallest turn taking `a`'s
  direction to `b`'s: the plane `b ∧ a` divided by `norm (a × b)`, times
  the angle `atan2 (norm (a × b)) (a · b)`, written as the dual of
  `−φ (a × b) / norm (a × b)`. Only directions matter, so `a` and `b` can
  have different dimensions. When `a × b` is exactly zero, a parallel
  pair gives the zero bivector. An antiparallel pair, for which every
  plane through `a` would do, gives half a turn in the plane through `a`
  and `e3`, or through `a` and `e1` when `a` is along `e3`. Vectors that
  are nearly parallel can be sensitive to numerical approximation. A zero vector divides by zero.
- Constructors build antisymmetric matrices from shared components and their
  negations. The wedge computes one triangle and negates it for the other,
  including under stochastic rounding. Chart generators are checked for
  antisymmetry in every realized value.
- `euler313 Ω i ω = expm (rotz Ω) @ expm (rotx i) @ expm (rotz ω)` is the
  matrix of the classical 3-1-3 sequence (the orbital elements' node,
  inclination and argument). It takes perifocal components to inertial
  ones. It returns the matrix, not a bivector, because two turns in
  different planes do not add as bivectors. Each Euler sequence is its own
  function, with the sequence in its name.

**Matrix exponential.** Both arithmetic implementations use scaling and squaring.
Each realization chooses its own scale. Rational kernels use precision-controlled
Taylor terms. Double kernels use twenty terms after scaling the norm below one half.
Zero maps exactly to the identity. General and sampled matrices use the same
mathematical operation. No residual enclosure is attached to the result.

**`transformBy R t`** contracts `R` into every axis of `t`: `R v` for a
vector, `R P Rᵀ` for a matrix such as a covariance, and `R` on each index
of a higher-rank tensor. So `transformBy R (a ⊗ b) == (R @ a) ⊗ (R @ b)`
and `transformBy R (transformBy S t) == transformBy (R @ S) t`. It keeps
`t`'s dimension and display unit. A number (rank zero) is returned as it
is. That every length of `t` is `n` cannot be written in the type (§4.3),
so it is checked when the call runs: "transformBy: every axis must have
length n: the matrix is 2 × 2 and the tensor's lengths are [2, 3]". Nor
can "along every axis" be said over axis sets (§3.9), so `R` has
anonymous axes. A chart's rotation, along two named sets, goes through
the typed forms instead: `rotateVec r v` (`r @ v`) and `rotateCov r p`
(`r @ p @ rᵀ`) in `linalg`.

**`contract`, `permute` and `slice`.** `contract i j t` sums `t` over the
diagonal of index positions `i` and `j` (0-based from the front of the
shape, as for `t.i`), which must have equal lengths. The result drops both
positions and keeps the dimension. The two positions can be written in
either order. `contract 0 1` of a square matrix is its trace, so the
library's `trace` is `Mat n n d -> Num d` at rank two and the partial
trace over the first two positions above it. The contracting product is a
contraction of the tensor product: `a · b` is `contract (r-1) r (a * b)`
for `a` of rank `r`.

`permute [p0, …, pk-1] t` reorders the first `k` positions of `t`, so
that position `q` of the result is position `p_q` of `t`. Positions from
`k` on stay where they are, and `permute [1, 0]` is `transpose` on a
matrix.

`slice k i t` keeps the components of `t` whose index at position `k` is
`i`, and drops that position: `slice 1 0` of a matrix is its first column,
and `slice 0 i t` is `t.i`. It is written `t._.i` with `k` wildcards
(§2.10).

All three are linear. Contraction sums realized components.
Slicing and permutation preserve component values and their sample identities.

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

**Indexed maps.** `vzipWith f a b` is the general form of `⊙`. It applies
the two-argument `f` to each pair of components of two tensors of one
shape. Unequal lengths are a type error ("lengths differ: 2 and 3"). Like
`vmap`, it gives a result with no display unit of its own. `indices v` is
the vector `[0, 1, …, n-1]` of exact dimensionless numbers, as long as
`v`. It reads only `v`'s length, not its components. The library's
`vimap` combines the two, so that a map can see each component's
position:

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

The position arrives as a value, a `Num`, never as a literal, so it cannot
be used where a literal is needed. `x ^ i` is a parse error, because an
exponent is an integer literal (§2.5). `v.i` reads a record field named
`i` ("unknown field `i`"), not a position (§2.10). `indices` is rank one
only, and a matrix argument is a type error.

`timap f t` is the indexed map at any rank. For each component of `t` it
applies `f` first to the component's multi-index, a vector of exact
dimensionless naturals with one entry per axis, read off the row-major
offset, and then to the component. The index's length is the rank of `t`,
written `Vec (rank s)` (§4.1), so inside `f` the index is an ordinary
vector, and `i.0`, `i.1` are ordinary projections with the usual static
bound.

**Mapping is lazy, and its dimension is typed.** `vmap`, `vzipWith` and
`timap` read the result's dimension off their own type as instantiated
where they are used (§8), never off a component. They evaluate each
result only when that component is read, and give the result no display
unit of its own. So `(vmap (\x -> 1/x) [0, 2]).1` is `0.5`, because the
division by zero in the other component is never forced. A map over an
empty tensor has the dimension the function gives:
`vmap (\x -> x * 1 m) ([] :: Vec 0)` is `[] m`. Inside a polymorphic function
the dimension is the caller's, passed as a type-level argument. `vimap`
stays the vector form with a scalar position, and `timap` is the general
one. A diagonal mask:

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
> diag [1, 2, 3]
error at 1:1
  diag [1, 2, 3]
  ^^^^
  expected Tensor (n : m : s), got Vec 3: a tensor of rank at least 2 against a vector
```

The projections inside `f` fix how much of the shape a definition needs:
`i.1` asks for an index of length at least two, so `diag` takes a tensor
of rank at least two. Applied directly, `timap (\i x -> i.1 * x) [1, 2, 3]`
is refused the same way at the vector.

**Printing** factors the common unit: `[1, 2, 3] m`, `[[1, 0], [0, 1]]`
printed as `[1, 0; 0, 1]` (§2.4). Sampled components print with separate empirical summaries.

**Implemented in:** `Metron.Eval` (`runPrim`, `matrixProduct`, `identityMatrix`, `rotateVector`, `positions`, `strides`, `unflatten`, `sized`), `Metron.Numerical.Rational` (`matrixExp`, `invert`, `determinant`, `choleskyRows`), `Metron.Rational` (matrix kernels), `Metron.Prelude` (`algebra`), `Metron.Core` (`lengthLimit`), `Metron.Primitive.Types` (`primScheme`, `primSchemeFor`).
**Tested by:** "products"; "contraction and permutation"; "slicing along an axis"; "rotations"; "types" › "indices, vzipWith and vimap (design §3.3)"; "types" › "timap's index is a Vec (rank s) (design §4.1)"; "end to end" › "a tensor past the components limit is refused when built"; "end to end" › "an empty tensor takes its element type from context"; "end to end" › "an empty tensor nothing fixes is a type error, not an internal one"; "separate sampling foundation".

### 3.4 Sampling compound values

**Decided.** Tensor components share input identities. A rotation of one sampled
vector preserves those dependencies through the complete nonlinear calculation.
Construct separate inputs with separate sample sites. A single site inside a
mapping function shares its latent variate across calls.

A sampled chart parameter gives each realization its own frame transformation.
A zero chart step in any realized input is invalid. No interval enclosure
can establish invertibility for unsampled inputs.

**Implemented in:** `Eval`, `Rational`, `Double`.
**Tested by:** "rotations", "frames", "separate sampling foundation".

### 3.5 Sample covariance

**Decided.** Covariance uses paired ordinary input realizations with denominator N−1.
`covariance` returns the component covariance matrix.
`crossCovariance` returns the paired block between two tensors.
`jointCovariance` builds the library's `Cov2` record from those blocks.
Shared samples preserve correlation. Distinct declarations provide independent
latent draws, whose empirical covariance need not be exactly zero.

Rounding repetitions do not contribute to these statistics.
Requested rounding analysis of a covariance reduction fails explicitly.

**Implemented in:** `Numerical.Statistics`, `Rational`, `Double`, `Prelude`.
**Tested by:** "separate sampling foundation", "independent arithmetic and grouped rounding".

### 3.6 Points and charts: affine quantities

Some quantities are **points**, not amounts: a temperature, an instant, an
electric potential, a position. Two points subtract to give the amount
between them, and an amount added to a point gives another point. Two
points have no sum, and a point has no multiple. Everything in §3.2 to §3.5
is about amounts, which form the vector space `Num δ`. Points form an
*affine space* over it. The language gives them their own type, `Point c`,
typed by the *frame* `c` they are written on (§3.10, part F), and two
operators of their own. So the arithmetic of points cannot be confused with
the arithmetic of amounts, just as each product of §3.3 has one symbol and
one type.

| written | type | meaning |
|---|---|---|
| `p .- q` | `Point c → Point c → Diff c` | the amount from `q` to `p` |
| `p .+ v` | `Point c → Diff c → Point c` | the point `v` beyond `p` |
| `p == q`, `p < q` | `Bool` | points of one frame compare |
| `p + q`, `k * p`, `p + v` | type errors | points have no sum and no multiple: use `.+` |

`.-` reads "from". `.+` and `.-` have the precedence of `+` and `-`.
`p .+ -v` is the point `v` before `p`. The one legitimate "sum of points",
the weighted mean, is `q .+ (p .- q) / 2`. `Diff c` is the amount type of
the frame's space: `Num K` for a temperature (§3.10, F4). Arithmetic on a
point is refused with "expected Tensor s d, got Point degC: an amount and
a point; a point has no sum, multiple or unit; use .+ and .-, or to with a
chart (design §3.6)".

**Spaces and charts.** A point lies in a *space*, declared with the type of
its amounts. A point is written and printed on a *chart* of the space. A
chart is a step unit and an origin, given against the space's base (origin
zero, the base unit as step) or against a parent chart (§3.10, F2 and F10).
The library declares these, among others (§7.7):

```
space ITS90 = Num K                     -- in temperature
unit  deltaC = K                        -- the Celsius step is the kelvin
unit  deltaF = 5/9 * 1 K                -- the Fahrenheit step
chart kelvin on ITS90                   -- the absolute scale
chart degC   on ITS90 at 273.15 K       -- 0 °C is 273.15 K from absolute zero
chart degF   on ITS90 at 459.67 deltaF step deltaF
chart degR   on kelvin step deltaF      -- Rankine: kelvin rescaled
chart J2000  on TT at 2451545 day step day   -- an epoch in Terrestrial Time
```

A chart declaration names a chart value. When the chart is on a space or
gives an origin, it also mints a *frame*, a type (§3.10, F3). A chart with
a step alone is a rescaling and shares its parent's frame. The quantity
rule accepts a chart after a literal: `20 degC` is `pointOn degC 20 : Point
degC`, the point twenty steps up the chart from its origin, held as `20 K`
above degC's origin. `°C` and `°F` are the unicode spellings of `degC` and
`degF`.

- A difference of two points written on one chart carries that chart's
  step unit: `77 degF .- 68 degF` is `9 deltaF`. A difference of points
  written on two charts of one frame prints in base units: with `chart
  mdegC on degC step mK`, `1000 mdegC .- 0 degC` is `1 K`.
- `20 degC .+ 5 K` and `20 degC .+ 9 deltaF` are both `25 degC`.
- Points on two frames do not mix. `20 degC .- 68 degF` is refused with
  "points on degC and degF: convert one with `to`". `p to degF`
  re-expresses a point on another chart of its space: `20 degC to degF` is
  `68 degF`.
- Rankine and kelvin are one frame, so `491.67 degR .- 0 kelvin` is
  `273.15 K` with no `to`.
- A chart's step and origin can be approximate. A point written on such a
  chart carries their sampled values like any other value.

**A step must be invertible.** A point prints with its step divided out
(§3.10, F6). Every realized chart step must be nonzero.
Double steps must also be finite. A failed check names the chart, for example
"chart collapsed has no invertible coordinates: its step is zero".
A sampled distribution is not a proof about inputs that were not realized.

A chart on such a chart inherits the refusal, and the message names the
parent. A **negative step** is allowed and reverses the chart's direction:
with `unit back = -1 m`, `chart flipped on origin step back` writes `3
flipped` for `-3 origin`, and `(3 flipped) .- (1 flipped)` is `2 back`,
that is `-2 m`.

**Printing.** A point prints as its coordinates on the chart it was written
on, with the step divided out, followed by the chart's name: `25 degC`,
`2451545 J2000`. Points are the one place where a display offset is needed,
and the only place where one is allowed. A *unit* is always a factor
(§3.2.12), which is why Celsius cannot be a unit.

**Why a type and not a cleverer unit.** `20 °C + 5 °C` reads as 25 °C if
the second is a rise, and as nothing if it is a temperature. With a
factor-and-offset "unit" it silently becomes `298.15 °C`. The
point/amount distinction is the information the arithmetic needs. It is
the same distinction as instant/duration, position/displacement,
potential/potential difference and absolute/gauge pressure. One type
covers them all.

**Points over vectors.** A space can be of vectors, `space GCRS = Vec 3 m`,
with base axes of its own (§3.10, F2). `chart site on GCRS at [100, 200, 0]
m` mints a frame. `[1, 2, 3] site` is the point with those coordinates on
it, and `:type [1, 2, 3] site` is `Point site`. `p .- q` is a displacement
`Vec GCRS m` along the base axes, because a translated chart has its
parent's axes. `p .+ v` moves a position. `p.0` is its first coordinate,
the amount `1 m`. `p to eci` re-expresses it on another chart of the space.
A chart can also name a parent chart, `chart antenna on site at [2, 0, 1]
m`, and turn its axes with `by B` (§3.8).

**Implemented in:** `Metron.Eval` (`runPrim`, `point`, `chartOf`, `invertibleStep`, `namedChart`, `coordinatesOn`), `Metron.Desugar` (`desugar`), `Metron.Infer` (`unifyFrame`, `decide`), `Metron.Prelude` (`stdlibSource`).
**Tested by:** "units"; "display units"; "spaces and frames (design §3.10, part F)"; "turnedCharts"; "movingCharts"; "standard library".

### 3.7 Mixed dimensions

An orbit determination state is a position and a velocity. The matrices a
filter needs over it, the covariance `P`, the state transition `Φ`, the
measurement matrix `H` and the gain `K`, have entries of several
dimensions: `P` has `m^2` in one corner, `m^2/s^2` in the other and `m^2/s`
between. Tensors are homogeneous (§3.3), so such a matrix is not a value.
There are two routes. Route B is built. Route A is written down so that it
can be built later without deriving it again.

#### 3.7.1 Route A: Hart's dimensioned matrices (the escalation path)

G. W. Hart (*Multidimensional Analysis*, 1995) characterises the matrices
of quantities that linear algebra can work with. The rules:

- **Well formed.** An `m × n` matrix of quantities is well formed (Hart's
  "multipliable") when its dimensions factor as `dim Aᵢⱼ = rᵢ · cⱼ` for a
  *row dimension vector* `ρ = (r₀, …, r_{m-1})` and a *column dimension
  vector* `γ = (c₀, …, c_{n-1})`. The factoring is unique up to moving a
  constant between them (`rᵢ·k`, `cⱼ/k`). So the **canonical form** pins
  `c₀ = 1`, which makes `rᵢ = dim Aᵢ₀`.
- **Literals.** A literal is admitted when its dimensions factor, and
  refused otherwise. `[[1 m, 1 s], [1 s, 1 m]]` needs `r₀c₀ = m`,
  `r₀c₁ = s`, `r₁c₀ = s` and so `r₁c₁ = s²/m`, not `m`.
- **Product.** `A · B` with `A = (ρ_A, γ_A)` and `B = (ρ_B, γ_B)` is
  defined when `A`'s column vector times `B`'s row vector is one constant
  dimension, `c_Aₖ · r_Bₖ = κ` for every `k`, so that the terms of each
  inner sum agree. The result is `(ρ_A · κ, γ_B)`.
- **Transpose.** `Aᵀ` swaps the vectors: `(γ, ρ)`.
- **Inverse.** A square `A = (ρ, γ)` has `A⁻¹ = (1/γ, 1/ρ)`. Entry `(i, j)`
  has dimension `1/(cᵢ rⱼ)`, so that `A A⁻¹` has `rᵢ/rⱼ`.
- **Determinant.** `det A` has dimension `Π rᵢ · Π cⱼ`, because every term
  of the Leibniz sum has one factor from each row and each column.
- **Identity.** The identity that `A A⁻¹` gives is `(ρ, 1/ρ)`. It is
  dimensionless only on the diagonal, and a plain dimensionless `I` only
  when `ρ` is constant.
- **Vectors.** `Vec n d` embeds as the `n × 1` case with all rows `d` and
  the single column `1`. A homogeneous `Mat m n d` is `((d, …, d), (1, …,
  1))`.

What building it takes:

- a type `DMat m n ρ γ` whose `ρ` and `γ` are type-level lists of
  dimensions of lengths `m` and `n`, a new kind, unified element by element
  by Kennedy's algorithm (§4.4) with variable tails, as shapes are (§4.1),
- `encType` tags for it in `data` declarations (§6.1),
- a second typing rule for every tensor primitive (`+`, `*`, `·`,
  `transpose`, `inverse`, `det`, the literals, projection, slicing),
- a printer that gives each entry its own unit instead of factoring one
  out (§3.2.10).

The estimate is several agent-weeks, and every piece touches inference,
lint or the hash. Route A shares its row and column machinery with the
matrices of axis sets (§3.9, decision 3), but the two stay separate
designs.

**Open.** Route A is not built. It starts only when the escalation signal
of §3.7.2 appears (§10).

**Implemented in:** not built.
**Tested by:** none: not built.

#### 3.7.2 Route B: blocks

The state is a tuple of homogeneous vectors, `(r, v)` with `r : Vec n d1`
and `v : Vec n d2`. Every matrix over it is a record or tuple of
homogeneous blocks. Hart's factoring says why that is always possible:
group the rows and the columns of a well-formed matrix by equal dimension,
and each block of the grouping is homogeneous. The claim this route rests
on:

> Every intermediate of a Kalman filter over a state that is a tuple of
> homogeneous vectors, measured by a homogeneous vector, is itself
> homogeneous, or a tuple or record of homogeneous blocks.

`Cov(xₐ, x_b)` has dimension `dₐ d_b`. A block `∂x'ₐ/∂x_b` of `Φ` has
`d'ₐ/d_b`. A block of `H` has `d_z/d_b`. `S = H P Hᵀ + R` has `d_z²`. A
block row of `K = P Hᵀ S⁻¹` has `dₐ/d_z`. `(I − K H) P` has `P`'s blocks
again. Each is one dimension per block.

The library (§7.7) holds the two-block case, in `linalg`:

```
data Cov2 n d1 d2 = Cov2 {rr :: Mat n n (d1^2), rv :: Mat n n (d1*d2), vv :: Mat n n (d2^2)}

jointCovariance (r, v)    = Cov2 {rr = crossCovariance r r, rv = crossCovariance r v, vv = crossCovariance v v}
propagateCov2 (Φ_rr, Φ_rv, Φ_vr, Φ_vv) p                       -- Φ P Φᵀ
innovationCov2 h_r h_v p r_meas                                 -- S = H P Hᵀ + R, H = [H_r | H_v]
gain2 h_r h_v p s_inv     = (k_r, k_v)                          -- K = P Hᵀ S⁻¹
updateCov2 (k_r, k_v) h_r h_v p                                 -- (I − K H) P
inChartCov2 c p                                                 -- each block turned to c's axes (§3.8)
```

The fourth block of `P` is `transpose p.rv`. With `P = [A, B; Bᵀ, C]` and
`Φ = [F₁₁, F₁₂; F₂₁, F₂₂]`, the block formulas are these. Each is derived by
multiplying the blocks out, and each is checked in the tests against the
sample covariance computed directly from the transformed realizations:

```
rr' = F₁₁ A F₁₁ᵀ + F₁₂ Bᵀ F₁₁ᵀ + F₁₁ B F₁₂ᵀ + F₁₂ C F₁₂ᵀ
rv' = (F₁₁ A + F₁₂ Bᵀ) F₂₁ᵀ + (F₁₁ B + F₁₂ C) F₂₂ᵀ
vv' = (F₂₁ A + F₂₂ Bᵀ) F₂₁ᵀ + (F₂₁ B + F₂₂ C) F₂₂ᵀ
S   = H_r A H_rᵀ + H_r B H_vᵀ + H_v Bᵀ H_rᵀ + H_v C H_vᵀ + R
K_r = (A H_rᵀ + B H_vᵀ) S⁻¹          K_v = (Bᵀ H_rᵀ + C H_vᵀ) S⁻¹
rr⁺ = A − K_r (H_r A + H_v Bᵀ)    rv⁺ = B − K_r (H_r B + H_v C)    vv⁺ = C − K_v (H_r B + H_v C)
```

- `propagateCov2` forms the block rows of `Φ P` first, so `rr'` is
  computed as `(F₁₁ A + F₁₂ Bᵀ) F₁₁ᵀ + (F₁₁ B + F₁₂ C) F₁₂ᵀ`, the same sum.
- `updateCov2` writes `H P` as `(P Hᵀ)ᵀ`, because `P` is symmetric. The
  reason: in `h_r @ p.rr`, with nothing else to fix `h_r`'s rank, `h_r`
  defaults to a vector (§4.2), while `transpose h_r` makes it a matrix.
- The record keeps only `rv⁺`. Its mirror `Bᵀ − K_v (H_r A + H_v Bᵀ)`
  equals `transpose rv⁺` exactly for the gain that `gain2` computes, and
  the scenario test checks that too.
- The matrix products are `@` (`·`), never `*`, which is the tensor product
  (§3.3).

`:type` prints these. The variable names are inference's, so `d` and `d1`
are not the record's `d1` and `d2`:

```
jointCovariance : forall n d d1. (Vec n d, Vec n d1) -> Cov2 n d d1
propagateCov2   : forall n m d d1 d2 d3. (Mat n m (d1*d2*d3/d^2), Mat n m (d1*d3^2/d^2), Mat n m d2, Mat n m d3) -> Cov2 m (d/d2) (d/d3) -> Cov2 n (d1*d3/d) d
innovationCov2  : forall n m d d1 d2. Mat n m d -> Mat n m d1 -> Cov2 m (d1*d2/d) d2 -> Mat n n (d1^2*d2^2) -> Mat n n (d1^2*d2^2)
gain2           : forall n m d d1 d2 s d3. Mat n m d -> Mat n m d1 -> Cov2 m (d1*d2/d) d2 -> Tensor (n : s) d3 -> (Tensor (m : s) (d1^2*d2^2*d3/d), Tensor (m : s) (d1*d2^2*d3))
updateCov2      : forall n m d d1 d2. (Mat n m d, Mat n m (d1^2/d2)) -> Mat m n (1/d) -> Mat m n (d2/d1^2) -> Cov2 n (d*d2/d1) d1 -> Cov2 n (d*d2/d1) d1
inChartCov2     : forall s (c : s) d d1. Chart c -> Cov2 c (d1/d) d -> Cov2 s (d1/d) d
```

All are polymorphic in both state dimensions. None works only for
particular `d1` and `d2`.

- `propagateCov2` is as general as it can be. `Φ` can change both
  dimensions and the length: input `Cov2 m D₁ D₂`, output `Cov2 n E₁ E₂`,
  with `Φ_rr : E₁/D₁`, `Φ_rv : E₁/D₂`, `Φ_vr : E₂/D₁`, `Φ_vv : E₂/D₂`.
- Read with the measurement's dimension `d_z`, `innovationCov2` has `h_r :
  d_z/D₁`, `h_v : d_z/D₂` and `S : d_z²`.
- `gain2` takes `s_inv` on the right of `@` only, so it accepts any tensor
  whose first axis has the measurement's length. With a matrix `S⁻¹` it
  gives `k_r : D₁/d_z` and `k_v : D₂/d_z`, the dimensions that `updateCov2`
  asks for.

A zero block needs its dimension. `Φ_vr` of the constant-velocity `Φ =
[I, Δt I; 0, I]` is `1/s`, written `[0, 0, 0; 0, 0, 0; 0, 0, 0] s^-1`, and a
range measurement's `H_v` is `[[0, 0, 0]] s`. A bare dimensionless zero
forces `d1 = d2`. The scenario in §12 writes its own `eye`, because
the library has no `identity`.

The field names `rr`, `rv` and `vv` are labels in `linalg` (`linalg.rr`),
and a field is looked up by its name alone (§2.3). So a root record with a
field `rr` shadows the library's, as any root name does (§7.7). After
`data Foo = Foo {rr :: Num}`, `p.rr` on a `Cov2` is refused with
"constructor Foo does not belong to Cov2 2 m (m/s)". The library's own
definitions are unaffected, because they are terms by hash. Field
completion after a dot offers the three names too.

**The escalation signal.** Route B stops being the cheaper route when
either of these appears in real use:

- a filter needs block formulas beyond 2×2 blocks: a state of three or
  more vectors of different dimensions, which needs `Cov3` and its six
  blocks, or a general n-block form.
- the inverse of a single matrix of mixed dimensions: a measurement vector
  of mixed dimension (range and range rate together) makes `S` itself a
  2×2 block matrix, whose inverse is a Schur-complement formula over the
  blocks.

Then route A (§3.7.1) is the next step.

**Implemented in:** `Metron.Prelude` (`covarianceData`, `covarianceBlocks`), `Metron.Rational` (`crossCovarianceRows`).
**Tested by:** "units"; "display units"; "spaces and frames (design §3.10, part F)"; "turnedCharts"; "movingCharts"; "standard library".

### 3.8 Charts: frames with an orientation

A chart (§3.6) has three parts: a step unit, an origin and an orientation.
With the orientation, one construct describes a temperature scale, a
surveyed site, an orbital frame and a rotating planet. A chart on a space
of numbers has no axes to turn, and nothing in §3.6 changes for it.

**The one representation.** A chart over a space of `Vec n δ` holds three
things: the step (a unit of the amount space), the origin (an amount from
its parent's origin) and a list of *generators* `B`. Each generator is an
antisymmetric `Mat n n`: the oriented plane of rotation, with the angle as
its magnitude (a bivector, in Grassmann's terms). The chart's axes are
those of its parent rotated by `exp B₁ · exp B₂ · …`. An axis-aligned chart
has no generators.

```
chart degC on ITS90 at 273.15 K                    -- a space, an origin
chart site on GCRS at [100, 200, 0] m              -- a space, an origin
chart lvlh on eci at r0 by B                       -- a parent, an origin, an orientation
chart pf   on eci by rotz Ω then rotx i then rotz ω            -- a sequence of turns
chart ecef t on eci by rotz (gmst t) spinning [0, 0, 1] * ω_e  -- moving
```

The statement is `chart name params… on parent [at origin] [step unit] [by
B [then B …]] [spinning ω]` (§3.10, F10).

**Why the generator and not the matrix.** The exponential of an antisymmetric
matrix is a rotation mathematically. Its inverse uses the negated generator.
Numerical evaluation can leave small round-trip residuals.
The matrix is computed once per chart value when first needed.
Each realized generator must pass the antisymmetry check.

**Every other description is a library function to a bivector**, so the
Euler, axis-angle and quaternion forms are sugar and carry their
conventions in their names:

```
rotz θ         = (θ to rad) / 1 rad * (e2 ∧ e1)   -- rotx, roty likewise; rotz (90 deg) turns x toward y
axisAngle n θ  = dual ((θ to rad) / 1 rad * (-n) / norm n)   -- 3D: the axis is the dual of the plane
rotation a b   = the bivector taking a to b, angle atan2 (norm (a × b)) (a · b)
```

An Euler sequence is several bivectors applied in turn, not one, and a
chart is turned by the sequence itself: `by rotz Ω then rotx i then rotz
ω` is the 3-1-3 sequence. `euler313 Ω i ω` in `linalg` is the composed
*matrix* `expm (rotz Ω) @ expm (rotx i) @ expm (rotz ω)`, for `@` and
`transformBy`. It is not a generator. Euler angles have gimbal lock and
twelve sequence conventions, so each sequence is its own function.
Quaternions double-cover (`q` and `-q` are one rotation), so they are for
input only and never stored. A 3D skew generator describes one plane and
angle; in higher dimensions a general bivector can contain several
independent planes. A logarithm need not be unique or continuous globally.

**Open.** A `fromQuaternion q`, the logarithm of the rotor for input only,
is designed and not built (§10).

**A chart's orientation is a list of generators.** Every 3D proper
rotation has a skew-symmetric logarithm, including a composed rotation.
However, `expm(A+B)` is generally not `expm A @ expm B` when the generators
do not commute. **Decided.** We retain a sequence to preserve the supplied
composition and uncertainty, without choosing a logarithm. `by`
takes generators applied in order, written with `then`. `by rotz
θ` is a list of one, and `by rotz Ω then rotx i then rotz ω` a list of
three. `then` is a separator in the chart statement only, after `by` and
outside brackets. An `if` inside a generator keeps its own `then`. The
parser makes a list literal of the generators, so the desugarer stays
syntactic and the Core is `mkChart {F} {A} parent {} {} {g₁, …} {}`, the
empty lists being the clauses not written (§3.10, F10). Every element is
checked antisymmetric. The inverse is the list reversed with each element
negated, so nothing needs a matrix logarithm or an orthogonality check on
rounded matrices. The chart keeps its rotation `R = expm B₁ · expm B₂ · …`
beside the generators, computed once per chart value when first used.

**Conversion.** `p to c` gives `p`'s coordinates on chart `c`: from its own
frame's `(o_F, R_F)` to the base and down, `R_c⁻¹ (o_F + R_F x − o_c) /
step_c`, with components along `c`'s axes. A displacement converts by the
rotations alone, a point by rotation and translation. A tensor of any rank
converts by the rotation along every axis, so a covariance block goes as `R
P Rᵀ` (§3.7). Charts form a tree. A chart names the chart its origin and
axes are given in, and at the root a space (§3.10, F2). `a to b` goes up to
the common ancestor and down, composing at the matrix level, since two
rotations in different planes do not add as bivectors. Shared origins and
rotations along the common path cancel before any uncertainty arithmetic
(§3.10, F6). A chart's parent comes after `on`:

```
space GCRS = Vec 3 m
chart eci       on GCRS                                       -- the root for positions
chart perifocal on eci by rotz Ω then rotx i then rotz ω       -- rotated, same origin
chart site      on eci at [6378, 0, 0] km                      -- translated
chart antenna   on site at [2, 0, 1] m by rotz (30 deg)        -- relative to site
```

A chart on a space is given against the space's base (origin zero, base
axes, the base unit as step). The parent is a reference to a definition,
so the chart tree and the namespace tree are unrelated, and renaming a
chart changes nothing. None of this needs route A of §3.7: a rotation is
dimensionless and a chart has one dimension on every axis, so every
conversion stays homogeneous.

**The translated tree.** Each clause runs to the next clause word, so an
origin built with an operator needs no parentheses (`at r0 + r0`), and a
function applied to a chart can stand in it. `by` is a word in this
statement only, so `by B * pi / 6` keeps its whole expression and `let by =
5` is a name everywhere else. The origin is an amount from the parent's
origin along the parent's axes. So `chart site on eci at [6378, 0, 0] km`
and `chart antenna on site at [2, 0, 1] m` put `[0, 0, 0] antenna` at
`[6378002, 0, 1] eci`:

- `[1, 2, 3] antenna to eci` is `[6378003, 2, 4] eci`, and converts back
  exactly to `[1, 2, 3] antenna`.
- `[1, 2, 3] antenna .- [0, 0, 0] site on site` is `[3, 2, 4] m`.

`:view` and `:edit` print `chart antenna on site at [2, 0, 1] m`, and a
turned chart with its `by`, the generators joined by `then`. Entering what
they print again gives the same hash.

**Turned charts.** Every chart keeps its *absolute frame*, its origin and
rotation from the space's base, so that no conversion walks the tree:

```
R_abs = R_parent_abs · expm B₁ · expm B₂ · …          -- I for a root; a chart with no by has its parent's
R_abs⁻¹ = … · expm (−B₂) · expm (−B₁) · R_parent_abs⁻¹  -- from the generators
o_abs = o_parent_abs + R_parent_abs · a               -- a: the amount the origin is given at, along the parent's axes
```

The origin `a` is an amount with its own unit (`[7000, 0, 0] km`), not a
count of the parent's steps, so a translated chart is exactly what it says.
A point holds its coordinates on its frame with the step applied (§3.10,
F6), `step · c`. `p to c` maps them through the base: `o_abs + R_abs x` up
and `R_abs⁻¹ (· − o_abs)` down. With `chart eci on GCRS` and `chart lvlh on
eci at [7000, 0, 0] km by rotz (90 deg)`, lvlh's x axis is eci's y:

- `[1, 0, 0] lvlh to eci` prints `[7000000.0000000000000…,
  1.0000000000000000000…, 0] eci`.
- `[7000000, 1, 0] eci to lvlh` prints approximately `[1, 0, 0] lvlh`.

Numerical round trips can leave small residuals. Compare those residuals
against an explicit tolerance appropriate to the arithmetic and scale.

**Displacements are along a frame's axes.** A point is held in its frame's
coordinates, so `p .- q` for two points on one frame is the difference of
their coordinates, exact, along the frame's axes. `[1, 2, 3] lvlh .- [0, 5,
0] lvlh` is `[1, -3, 3] m`, a `Vec lvlh m`, and `q .+ (p .- q)` is `p`.
Re-expressed along another chart's axes, a displacement turns by the
rotations alone: `([1, 2, 3] lvlh .- [0, 5, 0] lvlh) from lvlh to eci`
approximates `[3, 1, 3] m` (§3.10, F10).

**Tensors of higher rank.** `rotationOf c` (a primitive) is `R_abs`, whose
columns are `c`'s axes along the space's base axes. It is exactly the
identity for a chart that is not turned. Its type says so (§3.10, F5):
`rotationOf lvlh : Mat GCRS lvlh`, rows along the base, columns along the
chart.

- `v to c`, with `v` along the base axes, is `Rᵀ v`.
- `v from c to eci`, with `v` along `c`'s axes, is `R v`.
- Mathematically `R⁻¹ = Rᵀ`. Numerical matrices approximate this identity.
- A covariance turns as `R P Rᵀ`: `linalg.rotateCov (rotationOf c) p`.
  `inChartCov2 c p` does each block of a `Cov2` (§3.7) so, since a state's
  rotation is `R` on positions and velocities alike.
- `transformBy`, which applies `R` along every axis at once, is for
  anonymous axes only (§3.3, §3.9).

A coordinate of a point, `p.0`, is an amount along its frame's own axis,
the step applied, on any chart (§3.10, F5). A turned chart's rotation is
computed once per value, and a definition's value is shared by every
reference to it in one evaluation. So a chart named in a hundred
conversions computes `expm` once per generator and direction.

**Moving charts.** A chart that moves is a function from an epoch to a
chart, and the epoch is a point on a time chart (`unix`, `J2000`). The
chart statement takes parameters before `on`, exactly as `let f x = …`
does, and a `spinning` clause:

```
chart spinner t on eci by rotz (w * (t .- t0)) spinning [0, 0, 1] * w
```

This desugars to `\t -> mkChart {Frame} {Axes} eci {} {} {rotz (w * (t .-
t0))} {[0, 0, 1] * w}`. `Frame` and `Axes` are the constructors of the frame
and axis types that the declaration mints (§3.10, F3). They are inside the
lambda, so `spinner t` has one frame and one axis set for every `t`. The
*name* carries the chart flag. `:type spinner` is `Point unix -> Chart
spinner`.

- `spinning` is a word in this statement only, like `by`.
- It takes a `Vec 3 (rad/s)`. A literal is dimensionless, so a spin is
  written `[0, 0, 1] * w` or `[0, 0, 7.29e-5] rad/s`, not `[0, 0, w]`.
  `spinning [0, 0, 1]` is refused: "expected Vec 3 (rad/s), got Vec 3:
  dimensions differ by rad/s".
- The radian is stripped as `rotz` strips it, so the chart keeps `Vec 3
  (1/s)`: an angular velocity along the chart's *own* axes, relative to its
  parent.
- A spinning chart with no `by` has an empty list of generators and prints
  with no `by`.
- `:view spinner` prints `chart spinner t on eci by rotz (w * (t .- t0))
  spinning [0, 0, 1] * w`, the lambda's parameters before `on`, and `:edit`
  reads it back to the same hash.

**Applying a moving chart.** A chart declared with parameters is a *moving
chart*. The resolver reads that off its stored Core (a lambda), so a store
reload keeps it with no flag of its own. Where a chart goes, an
application whose head is a moving chart's name takes the chart at that
instant: `p to spinner t1`, `p to (spinner t1)`, `[1, 2, 3] (spinner t1)`,
and a parent `chart station t on (spinner t) at [6378, 0, 0] km by roty (30
deg)`. A moving chart's bare name where a chart is wanted is refused when
desugaring:

| written | message |
|---|---|
| `p to spinner` | "`spinner` takes arguments: apply it, as in p to (spinner t0)" |
| `[1, 2, 3] spinner` | "`spinner` takes arguments: a point is written on an applied chart, as in [1, 2, 3] (spinner t0)" |
| `chart bad on spinner` | "`spinner` takes arguments: apply it, as in chart arm t on (spinner t) at [1, 0, 0] m" |

A point on a moving chart converts from a configuration named with `from`,
`p from (spinner t1) to eci`, never from the one it was written with
(§3.10, F7). This makes the classic wrong-epoch mistake an error. An
instant prints as it was applied, `[1, 2, 3] (spinner (1000 unix))`, which
reads back. A state is converted by named library functions (below).

**Kinematics, composed through the tree.** A velocity seen from a moving
chart picks up transport terms. A moving chart states its angular velocity,
because differentiating `exp B(t)` needs automatic differentiation,
which the language does not have. Each chart value keeps, beside its
absolute frame, its absolute angular velocity `ω_abs` and the velocity of
its origin `v_o_abs`, both along the base axes, computed once per value
when first used. With `a` the amount the origin is given at along the
parent's axes, `R` the chart's own rotation `expm B₁ · expm B₂ · …`, `ω` its
own spin along its own axes, and `_p` the parent's absolute values:

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

Three primitives read these fields, each along the space's base axes
(§3.10, F5):

- `spinOf : forall s (c : s). Chart c -> Vec s (1/s)` is `ω_abs`.
- `originVelocityOf : Chart c -> Vec s (d/s)` is `v_o_abs` (a space in
  metres gives `Vec s (m/s)`).
- `originOf : Chart c -> Vec s d` is `o_abs`.

The first two are over three axes, and exactly zero when nothing here or
above spins. `R_abs⁻¹` is `v to c`: `R` is orthogonal, so the transpose of
its transpose approximates its inverse.

**States, in `astro`.** `astro` is not used by default, so its field labels
never meet a user's (`:use astro` first):

```
data State t r = State {epoch :: Point t, pos :: Vec r m, vel :: Vec r (m/s)}
velocityIn c st =
  (st.vel - originVelocityOf c - linalg.cross (spinOf c) (st.pos - originOf c)) to c
stateFrom c t pc vc = let r = rotationOf c @ pc in
  State {epoch = t, pos = originOf c + r,
         vel = rotationOf c @ vc + originVelocityOf c + linalg.cross (spinOf c) r}
```

- `pos` is the position as an amount from the space's base origin, and
  `vel` the velocity relative to the base, the inertial frame. Both are
  along the base axes.
- A state is typed by its epoch's frame and its space's base axes:
  `stateFrom lvlh (0 unix) …` is a `State unix GCRS`.
- `pc` and `vc` are along the chart's own axes, `Vec lvlh m`, so
  `velocityIn` and `stateFrom` refuse a vector of another frame.
- Their inferred types state the space constraint. `:type velocityIn`
  prints `forall (s1 : Space (Vec 3 m)) (c : s1) c1. Chart c -> State c1
  s1 -> Vec c (m/s)`.
- `velocityIn c st` is the velocity relative to `c`, along `c`'s axes.
  `stateFrom c t pc vc` is the inverse: a position `pc` (an amount from
  `c`'s origin along its axes) and a velocity `vc` relative to `c`, to a
  state at epoch `t`.
- Both take a chart *value*, so a moving chart is passed at the state's
  instant: `velocityIn (ecef st.epoch) st`.
- The formulas are library code, so `:view astro.velocityIn` shows them.
- `originOf` exists because `velocityIn` and `stateFrom` need the chart's
  origin from the base.

**Open.** Whether `State` holds its position as a point on a frame instead
of an amount from the base is the owner's to decide (§11).

**What the tests check.** The tests check physics, not the formulas echoed:

- A body fixed on `spinner t1`, with inertial velocity `ω × r` computed in
  the test, has `velocityIn` numerically close to `0`. `stateFrom` gives it `7000 km ·
  w · [−sin θ, cos θ, 0]`, computed by hand. A body at rest in the parent
  turns backwards on the chart.
- `stateFrom` then `velocityIn`, and the position read back, recover, to numerical precision, what
  went in, on a chart turned, offset and spinning under a spinning parent.
- A body fixed on `spinner` at `t1` and at `t1 + 1 ms`: the forward
  difference of its positions differs from the velocity `stateFrom` gives
  by approximately `3.64605795e-8` of the speed, which is `ω δt / 2`,
  the centripetal term.
- Two levels: a station under the spinning chart, turned and offset, has
  spin `ω` and origin velocity `ω × (R_p a)` by hand. A body fixed at the
  station, moving with `ω × (p − o_eci)`, is at rest relative to it. A dish
  spinning at 0.01 rad/s on the station agrees with a central difference of
  positions to `4e-13 m/s` (each component under `1e-11`). A spin left out,
  or not turned by `R`, gives an error of `0.01 m/s`, so the test tells
  them apart.

**Open.** Nothing checks that a declared spin is the derivative of the
rotation it goes with (§10).

**Sampling passes through.** A sampled spin rate changes each realized velocity.
For a body at a fixed radius, doubling that radius doubles the velocity deviation.
Sampled angles give correlated coordinate components through the same rotation.
The norm of a rotated vector remains constant up to numerical residuals.

**Charts are affine, and curvilinear coordinates are functions.** Polar and
spherical coordinates are not charts. The map is nonlinear, its
coordinates have mixed dimensions (`r` in metres, the angles in radians),
and differences of polar coordinates are not displacements. A `Point` on
such a chart breaks the law that `.-` exists to guarantee. They are
ordinary functions to a record of amounts, `toPolar v = Polar {r = norm v,
theta = atan2 v.1 v.0, …}`. Sampling evaluates them, so
`crossCovariance` of the result's components is the Jacobian-propagated
covariance with no extra machinery (§3.4, §3.7). Range, azimuth and
elevation from a station are `to` the station's chart, then such a
function.

**Open.** Curvilinear charts, and a declaration that bundles a pair of
conversion functions, are open (§11).

**What stays separate.** `unit` stays separate from `chart`, because a unit
is a basis element of a vector space and a chart puts coordinates on an
affine space. That distinction is what refuses `20 degC + 30 degC`.
Per-axis units in one chart (x in km, z in m) are a basis with mixed
dimensions, and wait for route A (§3.7.1).

**The pieces.**

- **The chart value** (`Metron.Eval.ChartOf`, the value constructor
  `VChart`) holds:
  - `name`, the name it was declared under, for printing,
  - `step`, and `stepHint`, the step's display unit, which differences
    inherit,
  - `origin`, the origin as an amount from the space's base origin along
    the base axes, and `localOrigin`, the declared offset along the
    parent's axes,
  - `dims` and `dim`, the shape and dimension of the space's amounts,
  - `parent`, the parent chart's *value*, not a hash (a chart need not be
    named, and the definition's Core already refers to the parent's
    definition by hash), or none for the base of a space,
  - `generators`, antisymmetric `n × n` matrices, row-major, applied in
    order,
  - the absolute frame, `rotation` and `rotationInverse`, lazy, and none
    when nothing here or above is turned,
  - `relativeRotation` and `relativeRotationInverse`, the cached local
    transforms that conversions below a shared ancestor use,
  - `spin`, its own angular velocity along its own axes in s⁻¹,
  - the absolute kinematics, `spinAbs` and `originVelocity`, lazy like the
    rotation, and none when nothing here or above spins,
  - `frame`, the hash of the frame it is a chart of: the one it minted, or
    a rescaling's parent's,
  - `moving`, whether that frame's chart takes parameters,
  - `applied`, the arguments of the moving chart an instant came from, for
    printing only (`Eq` ignores them).
- **`mkRoot` and `mkChart`** (§3.10, F10) build it from its clauses, each a
  list of none or one, the generators any number. Each generator is a
  dimensionless `Mat n n` over the chart's own axes. It is checked `B + Bᵀ
  == 0` exactly, entry by entry as `Bⱼᵢ == -Bᵢⱼ` in every realization. An
  approximate angle times an exact bivector passes. A sum `Bᵢⱼ + Bⱼᵢ` does
  not, since slack never cancels. A generator that fails is refused when
  the chart is used: "the generator of a chart must be antisymmetric: a
  bivector, such as rotz θ or a ∧ b".
- **`rotationOf : Chart c -> Mat s c`**, the absolute rotation, exactly `I`
  for an unturned chart, and `spinOf`, `originVelocityOf` and `originOf`
  (above). In `linalg`: `rotateVec r v` (`r @ v`), `rotateCov r p` (`r @ p
  @ rᵀ`) and `inChartCov2 c p`, a `Cov2` block by block.
- **`expm`** makes each generator's rotation (§3.3). It refuses statistical
  inputs, and so does a chart rotation evaluated through it (§3.3).
- **`transformBy`** applies a matrix along every axis, with anonymous axes
  only (§3.3).
- **The rotation constructors** in `linalg` (`e1 e2 e3`, `rotx`, `roty`,
  `rotz`, `dual`, `axisAngle`, `rotation`, `euler313`) are in §3.3. Every
  bivector they return is exactly antisymmetric.
- **Printing.** A chart's type is `Chart c`, its frame (`Chart lvlh`,
  `Chart degC`). A chart value prints as `chart J2000`. `:ls --charts`
  lists charts. `:view` and `:edit` print the statement with the clauses
  written, in the order `at`, `step`, `by`, `spinning`.

**Open.** These are not decided or not built (§10, §11):

- *An Earth chart.* None is shipped. That is the owner's decision.
- *Time scales.* No chart joins `TT` and `UTC`, and UT1 and TAI are not
  modelled.
- *Origins that move relative to their parent* get no velocity for that
  motion.
- *Library frames.* Whether `GCRS` and `eci` are library declarations.

**Axis sets.** Vectors typed by their axes are §3.9. A chart is an axis set
with an origin, and `p to lvlh` returns a `Point lvlh` whose differences
are `Vec lvlh m`.

**Implemented in:** `Metron.Eval` (`runPrim`, `chartOf`, `chartRoute`, `chartFrame`, `chartMotion`, `narrowChart`, `takesArguments`, `rotateVector`, `cross3`), `Metron.Desugar` (`desugar`, `refuseMoving`, `movingChart`, `chartResolution`), `Metron.Parser` (`chartStatement`), `Metron.Pretty` (`renderTermUnits`), `Metron.Prelude` (`stateStatements`, `algebra`), `Metron.Numerical.Rational` (`matrixExp`).
**Tested by:** "units"; "display units"; "spaces and frames (design §3.10, part F)"; "turnedCharts"; "movingCharts"; "standard library".

### 3.9 Axis sets: named positions and index types

Two layers: the first a sugar, the second a type-system extension.

**Layer 1, named positions.** This layer is designed and not built.
`axes x y z` declares labels for positions 0, 1, 2 in the current
namespace, persisted as label lines like fields, moved by `:rename` and
resolved through scope. `v.x` desugars to `v.0`: the same Core and the same
hash as the numeric form, so `:view` prints whichever was written, and
projection's static bound applies (`v.z` on a `Vec 2` is refused). It works
at any rank (`m.y.x` is row 1, column 0), and `linalg` seeds `axes x y z`.

**Open.** Layer 1 is designed and not built: `axes` is an unknown name and
`[1, 2, 3].x` is "unknown field `x`" (§10).

**Layer 2, axis sets as types.** Amounts carry the axes they are measured
along. So mixing components of two frames is a type error, and a
displacement taken inside a frame prints along that frame's axes. The
decisions, each with the rules that hold:

1. **An axis set is a static, type-level name.** §4.1 keeps terms out of
   types, so `Vec (ecef t)` cannot exist. A chart declaration with `by` or
   `spinning`, and a vector space (§3.10, F2), introduce one axis-set name.
   A moving chart has one axis set for all `t`: its axes turn, its identity
   does not. A plain length is the *anonymous* set of that size: `Vec 3` is
   `Vec (Anon 3)`. Two named sets never unify with each other, nor with an
   anonymous one.

   **Decided.** The identity lives in the content, not in the name.
   Without a stamp, two charts with the same body share a hash, and a
   stored value's type comes from its Core alone. A frame carried on the
   name is then lost the moment a value is stored. As with the owner stamp of a `sample`
   measurement (§3.2.4), the name enters the content:
   - Entering a chart with `by` or `spinning`, or a vector space, mints a
     nominal type with no parameters and one constructor with no fields,
     labelled `Axes "full.path"`. That label kind is one that no source
     `data` declaration can produce (§6.1), so `data Eci = Eci` never
     equals a chart's axes.
   - The desugarer passes the minted constructor to `mkRoot` or `mkChart`,
     and the primitive's scheme reads the axis set's hash from that
     argument, as `contract` reads its literal positions. A chart with
     neither `by` nor `spinning` shares its parent's axes and mints none.
   - The minted type is stored like a declared type and prints as its
     frame's or space's name. Types and terms are separate namespaces, so
     `lvlh` the chart and `lvlh` its axes coexist.
   - `:export` leaves the axes out, since the declaration mints them again.
   - Two charts with one body are two axis sets and two hashes. A moving
     chart mints inside its lambda body, so `ecef t` has one axis set for
     every `t`.
   - A chart moved by `:rename` or `:move` takes its axes with it, their
     stamp being its path. A chart redefined at its path keeps its axes. A
     chart redefined as no chart drops its axes' name.

2. **Size.** An axis set has a size: `card lvlh = 3`, `card (Anon k) = k`.
   `rank s` counts axis sets as it counts lengths. In the type language a
   shape position is a length (a literal, `n + k`, `rank s + k`) and a name
   slot beside it: anonymous, a named set (the hash of what declares it),
   or an axis variable, of the kind `Axis` (§4.1). `Vec (Anon 3)` is the
   position `3` with an anonymous slot. The `card a` above is the length
   beside the slot, so there is no `card` function and no `card`
   constraint: `card a ~ 3` is the literal `3` beside an axis variable `a`.
   `(length, axes)` below is notation, not syntax.

   The slot unifies syntactically: anonymous with anonymous, a name with
   itself, a variable with any slot (with the occurs check). Any other pair
   fails with a message naming both: "the axes of lvlh against anonymous
   axes", "the axes of GCRS against the axes of lvlh". Lengths are unified
   first, so a mismatch of lengths reports as one. Lint matches a slot as it
   matches a length: an instance substitutes axis variables too, and its
   type application is capture-avoiding.

3. **Matrices carry a row and a column axis set.** This is where the safety
   comes from. `rotationOf lvlh : Mat GCRS lvlh` (rows along the space's
   base axes, columns along lvlh's), and `@` requires the contracted axes to
   match. So `rotationOf lvlh @ v` with `v : Vec lvlh m` is a `Vec GCRS m`,
   and applying the wrong rotation is a type error: `rotationOf eci @ v` is
   "the axes of GCRS against the axes of lvlh". Route A for mixed
   dimensions (§3.7.1) needs the same row and column machinery for
   dimensions. The two share it in principle but stay separate designs.

4. **Points are typed by their frame and stored in their chart's
   coordinates.** **Decided.** `[1.5, 2.25, 3] lvlh : Point lvlh` is held
   as the three numbers `1.5, 2.25, 3` and the chart. Arithmetic inside a
   frame is exact, `p.0` is `1.5` along lvlh's x axis, and `q .- p` for two
   points on one chart is a `Vec lvlh m` (§3.10, F4 and F6). A point on a
   moving chart is held in that chart's coordinates too, so a point fixed
   on a moving body (a ground station) is a constant. Converting it out
   needs the chart's arguments, its time and any other parameters, so the
   wrong-epoch mistake is a missing argument and not a silent error.
   Points on different frames compare or subtract only after an explicit
   `to`, which is the typed conversion between them. Scalar points (`Point
   degC`) have no axes.

5. **Literals are polymorphic in their axes.** **Decided.** An unannotated
   literal vector gets a fresh axis variable, as an untyped numeric literal
   does in Haskell, so its frame comes from where it is used: `p .+ [1, 0,
   0] m` is along `p`'s axes, `[1, 0, 0] m + v` along `v`'s. A literal has
   no frame until it is used, so this is not a frame mix-up. A literal's
   positions, and a stack's new one, get fresh axis variables, carried in
   Typed Core (`TLit`, `TPack`).

   The restriction is on named values. Functions generalise over axis
   variables as usual (`let shift p = p .+ [1, 0, 0] m` is "the same frame
   as `p`"). A named value that is not a function does not keep a free axis
   variable: if nothing in its definition fixes its frame, its axes are
   anonymous. So `let offset = [0, 0, 2] m` cannot silently be a body-frame
   offset in one use and an inertial one in another.
   - A local `let` makes its free axes anonymous at its generalisation.
   - A definition makes them anonymous where its name is used (a use,
     `:type`, `:ls`). A stored scheme is its Core's alone and stays
     general, so a signature can keep a value polymorphic: `off :: forall
     (a : 3). Vec a m`. `forall a.` is a whole axis set, a length of its
     own included, and does not hold of a three-vector.
   - `:type e` is the type of `it`, a named value, so `:type off` prints
     `Vec 3 m` while `:ls off` prints its signature, `off : forall (a : 3).
     Vec a m`.
   - `e1`, `e2` and `e3` are anonymous where they are used.
   - An anonymous value that meets a named one is the unifier's axes error
     with a hint: `[1, 2, 3] lvlh .+ offset` is refused with "expected Vec
     lvlh m, got Vec 3 m: the axes of lvlh against anonymous axes; give it
     a frame with `withAxes c v`, or `v to c` if it is along its space's
     base axes".
   - `withAxes c v`, a primitive, reads an anonymous vector as along `c`'s
     axes, with no arithmetic. `v to c` re-expresses a vector that already
     has a frame along another chart's axes, which is a rotation and stays
     visible. A signature (`offset :: Vec body m`) also gives a frame.
   - An ascription narrows and never relabels (§4.8).

6. **`forall` is required, with kinds on binders.** **Decided.** A
   signature or an ascription that has type variables binds them with
   `forall` (or `∀`), followed by binders and `.` at the head of the type.
   Every other name in a type is a name and resolves like one, so a new
   unit called `d` cannot change the meaning of an existing signature. An
   unknown lowercase name is refused: "unknown name `a` in a type; bind it
   with forall if it is a variable". `forall` is a keyword.
   - A binder is a name or a sized `(a : 3)` (§2.7). `cross :: forall (a :
     3) d d1. Vec a d -> Vec a d1 -> Vec a (d*d1)` reads "any three-axis
     frame, the same one throughout". `offset :: forall a. Vec a m` is the
     deliberate opt-in of decision 5.
   - A binder shadows a unit, base unit or type of its name within its type
     (and, for a signature, within its body's ascriptions), never in an
     expression.
   - A `forall` scopes its variables over the body, so an ascription inside
     refers to the signature's frame. When an ascription names them, the
     body is checked wrapped in the signature, with the shared variables in
     a range of their own, and the signature is checked again on the
     result.
   - `:type`, `:ls` and every written-back signature (`:edit`, `:export`,
     `:scratch`, the `sig` line) print the `forall`, sized binders sized
     (`forall (a : 3) d. Vec a d -> Vec a d`), and read back as
     themselves. Errors, `:lint` and `:core` do not print it. `:view` shows
     a term or a declaration, never a scheme.
   - `:ls : type` queries stay implicit, being search patterns. `data`
     parameters are already explicit.

   §4.8 has the rules in full.

7. **The base axes are named.** **Decided.** A vector space names its base
   axes after itself (§3.10, F2). A root chart has its space's axes, a
   translated child shares its parent's, and a rotated child names its
   own. Two root charts on one space (`eci`, a lab bench) have one set of
   axes. Roots on two spaces never meet. Literals take their frame from use
   (decision 5). A named value with no frame of its own is anonymous and
   meets a frame through `to`, `withAxes` or a signature.

   **Written types.** A name in a length position resolves through the type
   scope to a minted axis type or a frame, and means that many positions
   along it: `Vec lvlh m`, `Mat GCRS lvlh`, `Cov2 lvlh m (m/s)`. The number
   is the frame's own, read off its stored type (`card lvlh = 3`), not a
   fresh length. A fresh length in a signature is a quantified variable,
   and with one `v :: Vec lvlh m` does not hold of a definition of three
   positions, and `:type`'s `Vec lvlh m` does not read back as itself. A signature, a
   data declaration or an ascription is read before the definitions of its
   group. So a group's charts, and what they depend on, are entered first
   for their labels alone, then the whole group. A chart and a signature
   that names its axes therefore read in one group (an `:export`, the
   REPL's pending definitions).

   **A written length variable is a whole axis set.** In a signature, a
   `data` declaration or a `:ls` query, a lowercase variable in a length
   position elaborates to a length variable and a companion axis variable,
   both quantified. A literal length is anonymous, and so is `rank s`,
   because an index's positions are numbers. A `data` parameter of kind
   length gains a companion axis parameter, numbered after the written ones
   and never printed, and its arguments are the axes of the length they go
   with. A sized binder is its literal length beside an axis variable of its
   own. Signatures are numbered in order of appearance, so a signature and
   the text it prints as are one scheme.

8. **Encoding.** The anonymous set of size `k` encodes byte for byte as a
   bare length `k`. A named set or an axis variable is a tag of its own
   (§6.1).

9. **The primitive schemes say which axes must match.** `slice`, `contract`,
   `permute` and `timap` move or drop axis sets as they move or drop
   lengths.
   - Elementwise operators share the whole shape. `outer` carries axes
     through `Append`. `dot` contracts the left's last position against the
     right's first, one length and one axis variable between them.
   - `transpose : Mat (n, a) (m, b) -> Mat (m, b) (n, a)` and `inverse :
     Mat (n, a) (n, b) -> Mat (n, b) (n, a)` swap rows and columns with
     their axes. `cholesky` keeps both.
   - `det` is over two axis sets of one size. `expm`, `wedge` and
     `covariance` are over one. `star` is over one set beside the literal
     `3`.
   - `crossCovariance : Vec (n, a) -> Vec (m, b) -> Mat (n, a) (m, b)`.
     `norm` and `indices` keep the argument's axes.
   - `contract`, `permute` and `slice` move or drop a position's axes with
     its length, `contract`'s pair sharing both. `timap`'s index `Vec (rank
     s)` is anonymous.
   - `cross`, `norm`, `rotx`, `roty`, `rotz`, the `Cov2` blocks (`Mat a a
     (d^2)`, `Mat a b (d*d1)`) and `timap` are generalised over axis sets.
   - `rotation`, `dual` and `axisAngle` print free axes of their own.
   - `transformBy` stays over anonymous axes, since no type says "every
     axis" over axis sets at any rank. `rotateVec` and `rotateCov` are its
     typed forms.

```
cross       : forall (a : 3) d d1. Vec a d -> Vec a d1 -> Vec a (d*d1)
norm        : forall n d. Vec n d -> Num d
rotz        : forall (a : 3). Num rad -> Mat a a
rotation    : forall d d1 (a : 3) (b : 3). Vec 3 d -> Vec 3 d1 -> Mat a b
axisAngle   : forall (a : 3) d (b : 3) (c : 3). Vec a d -> Num rad -> Mat b c
dual        : forall (a : 3) s d (b : 3) (c : 3). Tensor (a : s) d -> Tensor (b : c : s) d
det         : forall n a. Mat n a -> Num
withAxes    : forall (s : Space (Vec n d)) (c : s) (n : Len) d d1. Chart c -> Vec n d1 -> Vec c d1
rotationOf  : Chart c -> Mat s c                     -- rows along the space's base axes, columns along the frame's (§3.10)
p to c      : Point c -> Chart c1 -> Point c1        -- one space; a chart with parameters is applied, its source named with from
v to c      : Vec s d -> Chart c -> Vec c d          -- re-express a vector along a chart's axes: a rotation, visible
q .- p      : Point c -> Point c -> Diff c           -- one frame in, its axes out (Diff lvlh = Vec lvlh m)
v.0         : Vec a d -> Num d                       -- a has at least one axis
```

**Printing.** A named slot prints its name in place of the length (`Vec
lvlh m`), by hash and then through the driver's naming, as declared types
do. An anonymous slot prints its length. An axis variable beside a length
variable is that variable (one binder). One beside a literal is a sized
binder, `forall (a : 3) d. Vec a d -> …`. Any other, a second axis set
beside a length that has one, is a binder of its own (`det : forall n a.
Mat n a -> Num`). Errors, `:lint` and `:core` print a named slot by name
and an axis variable as its length.

**Open.** Six known gaps of axis sets, in the store log, chart origins, printing and one-pass groups, are listed in §10.3.

**Implemented in:** `Metron.Infer` (`unifyAxis`, `freshAxis`, `defaultValueAxes`, `generalise`), `Metron.Type.Syntax` (`tyLen`, `namedAxes`, `signatureScheme`, `enterData`), `Metron.Builtin` (`axesDef`, `axesHash`, `axesTag`, `mintedPath`), `Metron.Resolve` (`mintedBy`, `mintTypes`, `labelFrames`, `scopedSignature`), `Metron.Primitive.Types` (`primScheme`), `Metron.Type` (`renderScheme`, `defaultAxes`).
**Tested by:** "axis slots"; "named axes"; "forall"; "type annotations"; "rotations".

### 3.10 Units, spaces and frames

**Decided.** A point is typed by its *frame* (`Point lvlh`, `Point degC`),
and units are syntax, not values. The rules come in two parts: units (part
U) and frames (part F). Part F's `to` and quantity rule use part U's
machinery.

**The principle.** A chart is a step, an origin and axes. Each costs
something different to convert, and the type records exactly the parts
whose conversion is more than an exact multiplication:

| part | converting it | in an amount's type | in a point's type |
|---|---|---|---|
| step (scale) | multiply by an exact factor | no | no |
| origin | add an offset, possibly approximate or moving | no: it cancels | yes |
| axes | rotate, possibly approximate or moving | yes | yes |

Units are scale only, so a unit never enters a type. `1 km + 1 m` and `5
deltaC + 9 deltaF` add with no `to`, and `to` chooses the unit a result
prints in (`5 deltaC + 9 deltaF to deltaC` is `10 deltaC`). Between frames,
conversion is explicit, as Haskell makes conversion between types explicit:
`20 degC .- 68 degF` is refused until one side is converted with `to`.
Points never add (`20 degC + 5 degC` is refused), whatever their frames.

#### Part U: units are syntax

**U1. Units are not values.** An ordinary expression carries an amount
(`Num d`, `Vec n d` or `Tensor sh d`), a point, a chart or another value.
To pass a scale to a function, pass `1 km`, not `km`. `Unit δ` is internal
to elaboration and display: the evaluator keeps internal unit objects for
scale factors and display hints, and unit syntax lowers to them. The base
units `m kg s A K mol cd rad` are units by construction (§3.2.11). Charts
remain first-class values.

**U2. Arithmetic takes amounts.** Public multiplication, division and
powers operate only on amounts. Multiplication keeps the shape
concatenation rule of §4.2, and division takes a scalar denominator. At
generalisation an unresolved product still defaults its left operand to a
scalar, so `\a b -> a*b` is `forall d s d1. Num d -> Tensor s d1 -> Tensor
s (d*d1)`. A power of a unit is a unit, and a product or quotient of units
is a unit.

**The implicit one.** At an operand of ordinary `*` or `/`, a complete unit
expression is shorthand for one of that unit:

```
5 * km         = 5 * (1 km)
km / s         = (1 km) / (1 s)
x / km^2       = x / (1 (km^2))
x / (km/s)     = x / (1 (km/s))
```

The insertion is syntactic and respects local shadowing and namespace
resolution. It does not apply to other subexpressions, function arguments,
addition, comparisons, lists or tuples. Sections expand normally: `(* km)
3` is `3 km`. Named primitives such as `outer` take explicit amount
arguments.

**U3. A unit where an amount goes is refused.** `km`, `km + m`, `1 km +
m`, `f km`, `{km}`, `(km, 1)`, `outer km km` and `let u = s` are refused
with "a unit is not an expression: write an amount such as 1 km; bare
units are allowed at * and /, in quantity suffixes, after to, and in chart
steps". Write `1 km`, `1 (km^2)`, `1 km + 1 m` and `f (1 km)`. When the
desugarer recorded a hint at the span, it follows on a line of its own
(§4.7).

**U4. The quantity rule's readings.** Unit syntax after a literal (§2.6)
makes the amount `scale lit u`. A chart after a literal makes the point
`pointOn c lit` (§3.6, F8). Anything else is refused: `2 pi` is "`pi` is a
Num, not a unit or a chart: write the `*`". An expression after a
coordinate literal that is not declared unit syntax must be a chart, so
`\c -> 3 c` infers a chart over a scalar space, `forall (s : Space (Num d))
(c : s) d. Chart c -> Point c`. Where the spelling does not decide the
reading, inference does, and the reading is written into the term before
it is hashed. Core holds `scale` or `pointOn`, never the surface quantity
rule.

**U5. Unit operators bind before numbers: grouping precedes insertion.** A
quantity consumes the following chain of declared unit factors, and stops
at an ordinary value or at parentheses (§2.6). The implicit one (U2) is
inserted after the grouping:

```
4 km / 2 km   = (4 km) / (2 km)    -- 2
4 km / km     = 4 (km/km)          -- 4
(4 km) / km   = (4 km) / (1 km)    -- 4
1 / 2 m/s     = 1 / (2 (m/s))      -- 0.5 s m^-1
1 / 2 * m / s = ((1/2) * (1 m)) / (1 s)   -- 0.5 m s^-1
```

`unit u = s` creates a unit alias, which takes part in this grouping (`3 u`
prints `3 u`). `let u = 1 s` creates an ordinary amount and ends a quantity
suffix. `let u = km/h` creates an amount, `Num (m/s)`, that prints as `1 km
h^-1`, not a unit.

**U6. `to` reads its target by type.** `x to u` with unit syntax `u` is a
display conversion (§3.2.12). A chart target converts a point (F7) or an
amount along the chart's axes (F10). A dynamic `to` target is a chart, and
whether a point or a vector is converted is decided by types. An amount
after `to` is refused: `x to 1 km` is "an amount after `to`, which takes a
unit or a chart: write the unit, as in to km or to km/h". Where the types
do not yet decide, the reading waits, and an amount before a target still
unknown takes the unit reading.

**U7. Unit declarations.** `unit name = e` accepts a unit expression
(`unit speed = km/h`, `unit metre = m`) or a computed scalar amount (`unit
deg = pi / 180 * rad`, `unit dozen = 12`). The declaration makes its body a
unit and stores it with its name, scale and display hint. That the name is
a unit is label-level metadata (§3.2.12). Dimensions in types continue to
use unit names (§4.1). `:prefer` takes a unit too, through the same
unit-only elaboration as other unit contexts: `:prefer 1 km` is refused
with "expected unit syntax, such as km or km/s; a unit cannot be passed as
a value". Unit contexts are: quantity suffixes (`5 km/h`), display targets
(`v to km/h`), chart steps (`step km`), declarations, and `:prefer km/h`.

**U8. Printing and reading back.** A unit's own display hint is its
expression as written, so the unit `km/m` stays `km/m` until a quantity of
it is taken: with `unit r = km/m`, `:view r` is `r = km / m` and `5 to r`
is `0.005 r`, while `1 km/m` is the amount `1000`. A unit written twice is
one: `24 to dozen/dozen` prints `24`. The source printer reverses unit
construction in unit contexts, so declarations, exports and edits read
back with the same hashes: `:view speed` is `speed = km / h`, `:view km` is
`km = kilo * 1 metre`, and `let q = 3 * km` views as `q = 3 * 1 km`.

**U9. Units are internal.** No written type names a unit, and no type ranges
over both units and amounts. `Unit`, `Quantity` and `Amount` are refused in
written types:

| written | message |
|---|---|
| `a :: Unit m` | "units are syntax, not value types; pass an amount such as 1 km" |
| `b :: Quantity Amount m` | "quantities are amounts: use Num d or Tensor s d" |
| `c :: Amount` | "Amount is not a type: an amount is Num d, or Tensor s d" |

The type checker keeps a unit apart from an amount with a type of its own,
`Unit δ` (U1), internal to elaboration: a unit is one number, and only unit
syntax and a unit declaration have a unit's type. Arithmetic, equality and
comparison take amounts. `:ls` lists a unit with the type of one of it,
`unit kPa : Num (kg/(m*s^2))`, which reads back (§7.3). Applying a chart
still constructs a point, and points do not enter ordinary arithmetic.

**Implemented in:** `Metron.Desugar` (`regroup`, `quantityOf`, `staticUnit`, `bareUnit`, `desugarFactor`, `unitAmount`, `desugarUnit`, `quantityHints`), `Metron.Infer` (`decide`, `readingsOf`, `rewriteReadings`, `settleReadings`), `Metron.Resolve` (`withReadings`), `Metron.Eval` (`runPrim`, `unitOp`, `asUnit`, `asChart`), `Metron.UnitHint` (`mkHintAs`), `Metron.Pretty` (`renderTermUnits`), `Metron.Type.Syntax` (`tyType`), `Metron.Type.Base` (`Type`), `Metron.Session.Preferences` (`preferenceHint`).
**Tested by:** "units are syntax"; "internal units and public amount arithmetic"; "amount arithmetic"; "products" › "juxtaposition is for units and charts, by type"; "display units"; "standard library" › ":ls lists a unit with a type that reads back: one of it (design §3.10, U9)".

#### Part F: spaces and frames

**F1. Kinds.** There are two kinds for frames: `Space`, and `Frame s` for a
space `s`. `ITS90 : Space`, `degC : Frame ITS90`. In a binder a space names
the kind of its frames, so `forall (c : ITS90).` means `c : Frame ITS90`. A
bare `forall c.` used as a frame gets the kind `Frame s` with `s`
generalised too: a frame on any space, the way a `d` is inferred to be a
dimension. A binder names a frame's space, `(c : ITS90)` or `(c : s)`.

In a type, a frame is its identity (a minted frame's hash, or a frame
variable of kind `Frame`) beside two companions: its axes (`Axes c`) and
its space. A space is its identity (a declared space's hash, or a space
variable of kind `Space`) beside its shape (lengths only), its dimension
and its base axes. A named frame or space carries its companions as its
declaration fixed them, and a variable's companions are variables. So every
relation of F4 and F5 is unification and none needs a lookup: `Point c` and
`Point c1` meet by their identities, then by their spaces and axes. This is
a slot, as the axis slot is (§3.9), not general kind polymorphism.

`:type` prints a frame by its name and absorbs its companions: a frame's
axes print as the frame (`Vec c m`), a space's base axes as the space (`Mat
s c`). A space variable is a binder only when two frames share it or its
base axes are written, `forall s (c : s) (c1 : s)`. Otherwise the binder is
`forall c`.

**F2. Spaces are declared.** A space is a set of points that convert among
each other: the temperatures, the instants of time, a physical space.

```
space ITS90 = Num K
space TT    = Num s
space GCRS  = Vec 3 m
```

- `space Name = type` takes `Num δ` or `Vec n δ`. Anything else is refused
  with "a space is of numbers or of vectors, as in Num K or Vec 3 m".
- A declaration mints a nominal space, as a chart mints its axes. It is a
  type labelled with its path (a label kind of its own, `SpaceLabel`, §6.1),
  with two constructors: the tag a chart's Core names it by, and one that
  holds its amounts' type, so that a space's hash fixes what it is.
- Two spaces declared alike are two spaces, and points of one never
  convert to the other: `20 degC to eci` is "frames of two spaces, ITS90
  and GCRS: a point converts only to a frame of its own space".
- The declaration fixes the dimension and shape of the space's amounts and
  gives the space a base: origin zero, the base unit as step and, for a
  vector space, axes of its own, minted with it and named after it (`Vec
  GCRS m`). The base is the reference every chart on the space is given
  against in the end. No point is written on the base itself.
- A chart names its space as its parent: `chart degC on ITS90 at 273.15 K`,
  `chart JD on TT step day`. A chart with no `on` is refused (F10).
- A root chart is a translated child of its space's base and has the base's
  axes. So two translated roots on one space (`eci`, a lab bench) have one
  set of axes and convert with `to`, and two roots on different spaces
  never meet. A root can also be turned (`chart r on GCRS by rotz (10
  deg)`, with `rotationOf r : Mat GCRS r`).

**Decided. Naming spaces.** A space is named after the reference system
that pins it down, as astronomy names ICRS, GCRS and ITRS, never after the
bare quantity. `Time` or `Temperature` reads as the one global time, when a
space is one of possibly many. The library declares (§7.7):

- `TT` in `time` (Terrestrial Time), with `JD`, `MJD` and `J2000` (J2000.0
  is JD 2451545.0 TT).
- `UTC` in `time`, with `unix`, which counts UTC seconds without leap
  seconds. There is no chart between `TT` and `UTC`. They differ by a
  constant plus the leap seconds, so the map is not affine and is an
  ordinary function over a leap-second table, not a `to`. A `unix` instant
  and a `J2000` one are in different spaces, so mixing them is a kind error
  ("frames of two spaces, UTC and TT: …"), not a silent error of about 69
  s.
- `ITS90` in `temperature` (the International Temperature Scale of 1990),
  with `kelvin`, `degC`, `degF` and `degR`.

The library declares no pressure space. Absolute pressure is an amount with
a natural zero, and a gauge chart's 101325 Pa is a convention, so a user
who wants one declares it. User spaces follow the same rule: `space GCRS =
Vec 3 m`, `chart eci on GCRS`.

**F3. Frames.** A frame is the type-level identity of a chart: which origin
and which axes, with no numbers. Every chart has one. Whether a declaration
makes a new frame is decided by what it says, never by comparing values: an
origin can be approximate, and equality of computed values cannot be
decided.

- A chart directly on a space mints a frame. It is a root.
- A chart with `at` (a new origin) mints a frame.
- A chart with `by` or `spinning` (new axes) mints a frame and its axes
  (§3.9).
- A chart on a chart with only a `step` (`chart mdegC on degC step mK`,
  `chart degR on kelvin step deltaF`) is a rescaling. It shares its
  parent's frame, its points have the parent's type, and its step is only
  how they print. So Rankine and kelvin points subtract without a `to`. A
  rescaling mints no frame, and its name is refused where a frame goes:
  `Point degR` is "`degR` is a rescaling and shares the frame of its parent:
  write Point kelvin".

A frame is a type labelled `FrameLabel path moving` (§6.1), named after the
chart that mints it. So `chart degC on …` makes `degC` a value (`degC :
Chart degC`) and a frame (`degC : Frame ITS90`), in separate namespaces, as
a chart and its axes are. Two charts declared alike are two frames, like
two `newtype`s over one type. A chart with parameters mints one frame for
all its arguments: `ecef (100 J2000)` and `ecef (200 J2000)` are two chart
values of type `Chart ecef`. A chart redefined at its path keeps its frame,
as its axes do (§3.9). A chart moved by `:rename` takes its frame and axes
with it, re-stamped. The levels relate so:

```
20 degC          : Point degC          -- a point on the frame
degC  (value)    : Chart degC          -- the chart: its step and origin
degC  (frame)    : Frame ITS90         -- the type-level name and its kind
ITS90            : Space
```

**Decided. What a declaration means.** A chart declaration is one frame,
like one rigid body. Its parameters are that frame's configuration, its
degrees of freedom (a time, a joint angle, a state), and never a choice
between frames. It denotes the frame with a pose for each argument,
`pose(p) = (origin(p), rotation(p), step(p))` relative to the parent. A
point on it is coordinates in the frame, which do not depend on the pose,
as a seat's place on a train does not depend on where the train is. Two
bodies are two declarations. What they share is an ordinary function, not a
chart:

```
let lvlhTurn s = …                                   -- the recipe: a rotation for a state
chart lvlhA t on eci at (posA t) by lvlhTurn (stateA t)
chart lvlhB t on eci at (posB t) by lvlhTurn (stateB t)
```

`lvlhA` and `lvlhB` are sibling frames under `eci`, with axes of their own,
so their points and amounts never mix unconverted. One declaration used for
both, `lvlh (stateA t)` and `lvlh (stateB t)`, makes them one frame, and
then `b .- a` compares offsets from two spacecraft as if they were one
body. The checker cannot see that misuse, because it cannot compare
argument values. **Decided.** Charts are declared when the code is written.

**Open.** A frame per item of data is open (§11).

**F4. Types.** `Point c` is the type of points on the frame `c`, and `Chart
c` the type of charts whose frame is `c`: one value for a fixed chart, one
per argument for a moving one. Two type functions read a frame:

- `Axes c`, its axis set: a rotated frame's own, a translated or rescaled
  frame's parent's, a root's its space's. In a written type a frame's name
  in an axis position means `Axes c`, and a space's name the base axes.
- `Diff c`, the type of amounts between points on `c`: the space's
  dimension along `Axes c`. `Diff degC = Diff degF = Num K`, `Diff lvlh =
  Vec lvlh m`, `Diff bench = Vec GCRS m` for a translated chart.

`Diff` is a synonym, not a new type (an associated type, not associated
data). Amounts from frames with the same axes mix freely, because the scale
is applied into the value and the origin cancels. `Point` keeps the frame,
so `Point degC` and `Point degF` never unify. `Diff c` and the
dimensionless `Coords c` (what `pointOn` takes, F5) are one residual form:

- It reduces in substitution as soon as the space's shape is known, to the
  shape along `Axes c` in the space's dimension (or none, for `Coords`).
- A residual `Diff` against a tensor of known shape fixes the space's
  shape.
- Against a tensor of unknown shape it is a pending constraint `Diff c ~
  Tensor σ δ`, solved when either side is known. A point operation accepts
  a residual `Diff` as it is.
- One still pending when its definition is generalised is refused, since a
  scheme cannot carry it: "the amount between points on a frame of a space
  not known here: give a signature naming the space, as in forall (c :
  GCRS)". For example, `let mid2 p q = q .+ (p .- q) / 2` is refused so.

**Constraints on a space variable.** A binder can state a space's amounts:
`forall (s : Space (Vec 3 m)) (c : s). Point c -> Point c` is the type of
`let shift q = q .+ [1, 0, 0] m`. The space stays nominal and polymorphic,
and its shape and dimension are constrained. The amounts can be `Num d`,
`Vec n d`, or `Tensor sh d` with a shape variable, and their variables are
bound by the same `forall`. Printing includes these constraints when the
body alone does not reconstruct them. A length binder `(n : Len)` gives
`Vec n` anonymous axes, which lets `withAxes` keep the shared length
between its space and its input without giving the input a separate,
polymorphic axis identity.

**Declared types.** A `data` parameter used where a frame goes is a frame
parameter, with its companions as parameters after the written ones: the
axes of each length first, then each frame's axes and its space's slot,
shape, dimension and base. Its axes cannot be written in a declaration,
"… cannot be written in a declaration: no type says how many it has".

**F5. Primitives.**

```
pointOn    : forall c. Chart c -> Coords c -> Point c        -- 3 degC, [1, 2, 3] lvlh; Coords c dimensionless, along Axes c
(.-)       : forall c. Point c -> Point c -> Diff c
(.+)       : forall c. Point c -> Diff c -> Point c
pointAt    : forall c. Chart c -> Diff c -> Point c          -- the amount from the origin along Axes c: [0, 0, 0] c .+ v, at any shape (7.7)
to         : forall s (c : s) (c1 : s). Point c -> Chart c1 -> Point c1
p.k        : Point c -> Num δ                                -- the k-th coordinate, the step applied
rotationOf : forall s (c : s). Chart c -> Mat s c            -- rows along the space's base axes, columns along c's
originOf   : forall s (c : s). Chart c -> Vec s δ            -- the origin from the space's base origin (§3.8)
```

`withAxes`, `spinOf`, `originVelocityOf`, `velocityIn`, `stateFrom` and
`astro.State` are typed over frames and spaces in the same way (§3.8). The
checker needs no special rule for "convert first". `.-` takes two `Point
c`, so points on two frames fail to unify, reported as "points on degC and
degF: convert one with `to`". A different origin is two frame names that do
not unify, different axes are an `Axes` mismatch inside `Diff`, and a
different scale alone cannot fail. `pointAt site ([1, 2, 3] m)` is `[1, 2,
3] site`. `pointAt` places a computed amount on a chart from its origin, in
place of `[0, 0, 0] c .+ withAxes c v`.

**F6. Storage: chart coordinates** (§3.9, decision 4). A point holds its
coordinates on its frame with the step applied: an amount from the frame's
origin along the frame's axes in base units, and its chart, for printing.
`20 degC` holds `20 K` above degC's origin. `p.k` reads a coordinate, an
amount in the chart's step unit on a space of one axis set. Printing
divides by the step, so a point prints on the chart it was written on with
no other arithmetic. Applying the step is an exact multiplication. The
origin and the rotation, where error and motion come from, are applied only
by `to`, so arithmetic inside a frame never passes through them. `.-` and
`.+` within a frame are coordinate arithmetic. A point written on a
rescaled chart and one on its parent are on one frame and subtract
directly.

The chart value holds its frame's hash and whether that frame takes
parameters (§3.8). `to` between charts of one frame relabels. Between
frames it follows local transforms up to the common configuration and
down. Configurations match by frame identity and structurally identical
local offsets and generators along their common path, never by
approximate equality. Shared origins and rotations cancel before
uncertainty arithmetic. Without a shared configuration the path reaches the
space's base, giving `R_T⁻¹ (o_F + R_F x − o_T)`.

**F7. Charts with parameters.** A chart's parameters are arbitrary, any
number of any type. An applied chart fixes its whole path to its space,
because a child's declaration either applies its parent to expressions of
its own parameters (linked: `chart lvlh s on (ecef s.epoch) at s.pos by
…`), or leaves the parent's parameters open, and they become parameters of
the child (inherited: `chart arm q t on (ecef t) at [1, 0, 0] m by roty
q`). So a conversion needs exactly two chart values, the source's and the
target's.

A point on a parameterised frame holds its coordinates, and the chart it
was written on for printing only. Writing one needs an applied chart,
`[1, 2, 3] (ecef t0)`, because the step can depend on the arguments.
Converting names the source chart whenever it takes parameters, and a
parameterised target is given applied:

```
p from (lvlh s) to eci     -- p : Point lvlh
q to (ecef t)              -- the target applied
r to eci                   -- r on a chart without parameters: no from
p to eci                   -- refused: "lvlh takes arguments: write p from (lvlh …) to eci"
```

`p from c to c1` is typed `Point f -> Chart f -> Chart f1 -> Point f1`: the
chart after `from` must have the point's frame. The chart a point was
written on is never used for a conversion, so a wrong configuration is a
missing argument, not a silent error. A `to` from a frame whose chart
takes parameters is refused when its frame is known, with the operands as
written ("spinner takes arguments: write p from (spinner …) to eci"). When
only a frame variable is known (`toE :: forall (c : GCRS). Point c -> Point
eci`), it is refused at run time with "… takes arguments: write p from (…
…) to c", never read off the chart a point was written on.

`.-` on one frame is frame-relative, whatever configurations its points
were written with. The other questions one asks of two points are
conversions followed by a subtraction:

1. On one frame: `b .- a`, relative to the frame (two cities on `ecef`).
2. Across the tree: `(sat to (ecef t)) .- station`, a satellite seen from a
   ground station, in Earth-fixed axes.
3. Both in a third frame. At one configuration this re-expresses the
   difference: `(b to (lvlhA t)) .- (a to (lvlhA t))`, which equals `(b .-
   a) to (lvlhA t)`. At two configurations it is a new quantity that
   includes the frame's motion between them: `(b from (ecef t1) to eci) .-
   (a from (ecef t0) to eci)`.

`b .- a on (lvlhA t)` is shorthand for the first form (F10). It covers only
points that share a configuration.

**F8. The quantity rule for charts** (U4). Any expression of type `Chart
c` after a literal builds a point, so chart parameters, applied charts
(`[1, 2, 3] (ecef t0)`) and local chart values need no declaration. A bare
number is a coordinate only on a space of numbers, so a signature must say
so: `pt :: forall (c : ITS90). Chart c -> Point c` with `pt c = 3 c` holds,
and `pt :: forall c. Chart c -> Point c` is refused as not as general as
its signature, since `forall c` ranges over every space. Without a
signature the parameter is inferred to be a chart over a scalar space,
`forall (s : Space (Num d)) (c : s) d. Chart c -> Point c`. A chart with
parameters, unapplied, is a function and is refused after a literal (§3.8).
The `chart` keyword is still what mints a frame.

**F9. Printing and encoding.** `:type 20 degC` is `Point degC`, `:type
degC` is `Chart degC`, and `:type [1, 2, 3] lvlh` is `Point lvlh`. A point
prints `20 degC`, `[1, 2, 3] lvlh`. Spaces and frames are minted nominal
types, like a chart's axes, with label kinds of their own that no source
`data` produces. A type that mentions them encodes them as appended tags
(§6.1), and the store format moves if the encoding does. `:ls --types`
lists a frame as `frame degC` and a space as its declaration, `space ITS90
= Num K`. Plain `:ls` leaves frames out, as their charts list. Minted axes
print as their frame's or space's name. Type errors about frames say "a
point and a chart are typed by a frame, a chart's name or a variable, as in
Point degC" for `Point (Num K)`, and "unknown frame `K` in a type" for
`Point K`.

**F10. Syntax.** **Decided.** A chart declaration is its name, its
parameters and its clauses, with no `=`:

```
chart name params… on parent [at origin] [step unit] [by B [then B …]] [spinning ω]
```

- `on` is required and comes first. It ends the parameters and names the
  parent, a space or a chart (applied, if it has parameters). A chart with
  no `on` is refused: "name its space: `chart … on ITS90`, or the chart it
  is on, after its parameters".
- The other clauses come in any order, each running to the next clause
  word outside brackets, so no expression in them needs parentheses. A
  clause given twice is refused: "a chart has one `at` clause".
- `space`, `on`, `at` and `from` are keywords. `on` also subtracts in a
  frame (below). `step`, `by`, `then` and `spinning` are words only inside
  a chart declaration and stay free as names elsewhere.
- An omitted clause is inherited: the origin and the axes are the parent's,
  and the step is the parent's or, on a space, the space's base unit. Which
  clauses appear decides whether a frame is minted (F3).
- `unit` and `space` keep their `=`, since each binds one expression.

The library's charts, and §3.8's examples, read:

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

The last line works for a state whose position is along `ecef`'s axes.
With `astro.State`, whose position is along the base axes (§3.8), the origin
is `(s.pos - originOf (ecef s.epoch)) to (ecef s.epoch)`.

**Core.** Two primitives and no new Core constructor: `mkRoot frame {axes}
space {step} {origin} {generators…} {spin}` on a space, and `mkChart
{frame} {axes} parent {step} {origin} {generators…} {spin}` on a chart.
Each clause is a list of none or one (the generators any number), so that
which clauses are written is in the term and an omitted one is inherited.
Their schemes are computed from those lists and the tags, as `contract`'s
are from its positions, and `mkRoot`'s from the space's declaration (§4.3).
`:view` prints the clauses in the order `at`, `step`, `by`, `spinning`, and
every chart reads back to its hash. At run time a space's declaration is
looked up by hash for the shape and dimension of an omitted origin and
step.

**`to` is the one conversion.** It re-expresses its left side in the target
on its right, the reading chosen by types (U6):

- an amount in a unit (display),
- a point on a chart (F7),
- an amount along a chart's axes, where only the rotation applies, `(b .-
  a) to (lvlhA t)`.

The third reading (`toAxes`) takes an amount along the space's base axes,
on its leading position: `[1, 2, 3] m to lvlh`. `v from c0 to c1`
(`axesFromTo`) takes one along `c0`'s axes, and `p from c0 to c1`
(`fromTo`) a point. An amount carries no chart, so an amount along a turned
frame's axes is converted with `from` even when that frame takes no
parameters: `(b .- a) to eci` with `b` and `a` on a turned `lvlh` is "the
axes of lvlh against the axes of GCRS". The reading is chosen by the
value's type once the target is a chart. A value still unknown is
ambiguous at generalisation. `x to a to b` chains from the left: `(x to a)
to b`. `withAxes c v` labels a vector that has no frame, which is not a
conversion.

**Decided. Subtracting in a frame: `on`.** `b .- a on c` is `(b to c) .- (a
to c)`: both points converted to one frame at one configuration, then
subtracted, `b .- a on (lvlhA t) : Vec lvlhA m`. `on` binds like `to`, its
left side must be a `.-`, and it is a keyword, the same word as a chart
declaration's parent clause, meaning "relative to" in both. `in` cannot
serve, because `let d = b .- a in (lvlhA t)` already parses as a `let …
in`. `b .-
a on c` desugars to `let x = c in (b to x) .- (a to x)`, one chart value for
both, and prints so (`:view` of `let dd a b = b .- a on eci` is `dd = \a ->
\b -> let x = eci in (b to x) .- (a to x)`). It reads back to its hash. A
point on a frame with parameters still needs its configuration, so `on`
covers only points whose conversion needs no `from`. Otherwise the
desugared `to` is refused as F7 says, and the subtraction is written out.

**Open.** A frame per item of data (§11.3), constraints over `Diff` beyond the pending one, printing values with `·`, a `data` declaration that names a chart's axes in one group with the chart (§10.3), and whether `astro.State` holds a point (§11.3).

**Implemented in:** `Metron.Parser` (`chartStatement`), `Metron.Desugar` (`desugar`, `spaceNamed`, `refuseMoving`), `Metron.Infer` (`unifyFrame`, `unifyFrameSlot`, `unifySpace`, `overTensor`, `decide`), `Metron.Type.Syntax` (`enterSpace`, `tyFrame`, `chartTypeFrame`), `Metron.Builtin` (`spaceDef`, `spaceOf`, `frameDef`, `frameHash`, `frameTag`, `frameDefMoving`), `Metron.Resolve` (`mintedBy`, `mintTypes`, `labelFrames`), `Metron.Eval` (`runPrim`, `chartRoute`, `takesArguments`), `Metron.Primitive.Types` (`primScheme`), `Metron.Pretty` (`renderTermUnits`).
**Tested by:** "spaces and frames (design §3.10, part F)"; "named axes"; "dimension syntax" › "a point or chart takes a frame"; "turnedCharts"; "movingCharts".

## 4. Type system

The type system is Hindley-Milner with let-polymorphism. It is extended with
dimensions after Kennedy ("Programming Languages and Dimensions", 1996, and
"Types for Units-of-Measure", 2009), with type-level shapes for tensors, with
name slots for axis sets (§3.9), and with frames and spaces (§3.10, part F).
Inference carries a few constraints that it cannot solve at once and defers:
shape concatenation for the products, rank equations, the equality and
ordering instances (§4.2), and the relation between `Diff c` and a tensor
(§3.10, F4).

### 4.1 Types

```
τ ::= Tensor σ δ | Point φ | Chart φ | Diff φ | Coords φ | T a… | τ -> τ | α
a ::= τ | σ | δ | ν | χ | φ | ς      -- an argument of a declared type T, by the kind of its parameter
σ ::= [] | ν·χ : σ | s                 -- a shape: a list of positions, each a length and a name slot, possibly ending in a shape variable
χ ::= _ | A | x                         -- a name slot (§3.9): anonymous, a named axis set (a chart's or a space's minted type), or an axis variable
φ ::= F | c                             -- a frame (§3.10, F1): a chart's minted frame, or a frame variable, of kind Frame ς
ς ::= S | s                             -- a space: a declared space, or a space variable, of kind Space
δ ::= 1 | B | d | δ·δ | δ⁻¹             -- an abelian group, normalised
ν ::= k | n | n + k | rank s + k        -- a literal, a length variable, a variable plus a literal offset, or the rank of a shape variable plus an offset
```

`Num δ` abbreviates `Tensor [] δ`, `Vec ν δ` abbreviates `Tensor [ν] δ`, and
`Mat μ ν δ` abbreviates `Tensor [μ, ν] δ`. An open shape prints and parses
as `Tensor (n : s) d`, and longer chains as `Tensor (n : m : s) d`.

`Point c` is a point on the frame `c`, and `Chart c` is a chart of that
frame, which writes and prints its points (§3.6, §3.8, §3.10, F4). `Diff c`
is the amount between two points on `c`: the space's amounts along `Axes c`.
`Coords c` is the dimensionless coordinates a point is written with. A frame
carries its axes and its space as companions, and a space carries its shape,
its dimension and its base axes. The companions are known for a named frame
and are variables beside a frame variable (§3.10, F4). So `Diff c` reduces to
a tensor once the space's shape is known (`Diff degC = Num K`, `Diff lvlh =
Vec lvlh m`), and it stays residual before that. In a written type, a
frame's name where a length goes means its axes (`Vec lvlh m`), and a space's
name means its base axes (`Vec GCRS m`). `:type 20 degC` prints `Point
degC`, and `:type \p q -> p .- q` prints `forall c. Point c -> Point c ->
Diff c`. A binder names a frame's space: `forall (c : ITS90)`, `forall s (c :
s) (c1 : s)`.

`Unit δ` is internal to unit elaboration and display (§3.10, U1). It is not a
type that a user can write, and no type ranges over both units and amounts
(§3.10, U9). Ordinary arithmetic takes amounts.

#### Dimension syntax

**Decided.** A dimension is an ordinary type argument. Square brackets mean
one thing in a type, a shape (`Tensor [2, 3] m`), as they mean a list of
numbers in a vector literal.

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

- **Inside the parentheses** a dimension is a unit expression. It has names
  (base units, declared units, `forall`-bound dimension variables), products
  with `*` or `·`, `/`, powers with `^k`, `^-k` or superscripts, parentheses
  for grouping, and `1` for the identity. `*`, `·` and `/` share one
  precedence and associate to the left, as in an expression, so `m/s*kg` is
  `m·kg/s`. A dimension is a bare name only when it is one name to the first
  power. Anything else is in parentheses.
- **A name in a dimension position** is a dimension variable when a `forall`
  or a `data` parameter binds it. Otherwise it is a unit, which means its
  dimension: `Num km` is `Num m`, and `Num N` is `Num (kg·m/s^2)`. The type
  constructor fixes which arguments are dimensions: the last argument of
  `Num`, `Vec`, `Mat` and `Tensor`, and a declared type's parameters of kind
  dimension. The required `forall` (§4.8) makes the bare spelling
  unambiguous. `Point` and `Chart` take a frame: `Point degC`, `Chart degC`
  (§3.10, F4).
- **`·` is a token of its own.** In an expression, `·` and `⋅` are the
  contracting product, as `@` is, and the unicode echo writes `·` for `@`.
  In a dimension, `·` and `*` (and `⊗`, which lexes as `*`) are the product,
  and `@` is refused: "`@` is the matrix product; a dimension's product is *
  or ·".
- **Refusals.** These are the messages:

  | Written | Message |
  |---|---|
  | `Num (m s)` | "a dimension's product is written with * or ·, not by juxtaposition: write m*s" |
  | a bracket, or anything else, where a dimension goes | "a dimension is a unit, a variable, 1, or a product of them in parentheses, like (m/s^2)" |
  | `Point K` | "unknown frame `K` in a type" |
  | `Point (Num K)` | "a point and a chart are typed by a frame, a chart's name or a variable, as in Point degC" |
  | `Vec m` | "`m` is a unit, not a length: a vector's length comes first, Vec 3 m" |
  | `Num m^2` | a parse error: a power outside parentheses does not parse |

  The resolver gives the juxtaposition message for an application. The
  parser gives it for a power followed by a name, as in `(m^2 s)`.
- **Printing** follows the same rule, so what `:type` prints reads back as
  itself. Positive powers come first, in the customary order (`kg m s A K mol
  cd rad`, variables last), then `/` and the negative powers, grouped when
  there are several: `Num (kg*m^2*d/(s^2*K))`. With unicode on, the printer
  uses `·` and superscripts. With unicode off, it uses `*` and `^`. The
  printer never writes a negative power, but `^-k` and `⁻ᵏ` read. A dimension
  that stands alone in an error message prints without the outer
  parentheses: "dimensions differ by m/s". A point or a chart as a declared
  type's argument is in parentheses, `Q (Chart degC)`. Typed Core's type
  applications print the argument form, `sq @(m/s)`, `sq @1`.
- **Values print** `9.81 m s^-2`. A value's units are a display spelling of
  the value, not a type, and keep the juxtaposed form (§3.2.12).
- **The highlighter** colours a unit where a dimension goes, as an argument
  (`Num m`) or a factor of a product (`(m/s^2)`). It leaves a name in a
  type's place plain (`(g → m) → {g}`). A `data` declaration's parameters are
  variables there, as `forall`'s are (§7.3).
- **Queries** (`:ls : Num d -> Num d`) stay implicit. `d` is not a unit of the
  library, so an unknown lowercase name in a query is a variable (§4.8).
- **Errors name variables as `:type` does.** `:type`, `:ls`, the `sig` line,
  and error printing (unifier errors, "not as general as its signature",
  lint) skip a name that the same type prints as a base symbol. Each name
  appears once, and no variable has a base symbol's name: `Mat n k -> Mat n k
  m`, never a length `m` beside metres. `:type \x -> x * 1 s` prints `forall
  s1 d. Tensor s1 d -> Tensor s1 (s*d)`.

#### Declared types and the built-in data

A declared type `T` (§2.3) is a type constructor with parameters of fixed
kinds, known from its definition. `T a…` applies it to one argument for each
parameter. Two applications unify when they are of the same type (the same
definition hash, §6.1) and their arguments unify kind by kind. A declared
type is identified by the hash of its definition, not by its name. The driver
names a type that inference prints as `#a3f9k` (§7.2).

`Bool`, `(τ, τ, …)` and `{τ}` are not forms of their own. They are `T a…` on
the hashes of the three declarations that the compiler holds (§2.3). `Bool`
has no arguments, a tuple of `k` components is the tuple type of arity `k`
applied to them, and `{τ}` is the list type applied to `τ`. They are written
and printed in their own syntax, by hash, whatever names them. `Bool` in a
written type is the built-in one. Unification, equality, exhaustiveness and
lint treat them as any declared type. One exception: two tuples of different
arities fail with "expected a tuple of 2 components, got one of 3".

#### Kinds

There is one namespace of variables, and each variable has a kind: `Type`,
`Len`, `Shape`, `Dim`, `Axis` (the name slot of a shape position, §3.9),
`Frame` and `Space` (the identities of a frame and a space, §3.10, F1). Each
kind is an index domain with its own equational theory and its own unifier:

| Kind | Unifier |
|---|---|
| `Type` | syntactic |
| `Len` | the offset rule and the rank rules (below, §4.2) |
| `Shape` | element-wise, positions in order |
| `Dim` | Kennedy's algorithm (§4.4) |
| `Axis` | syntactic (§3.9) |
| `Frame`, `Space` | by identity, then the companions (§3.10, F4) |

A written length variable stands for a whole axis set: a length variable and
a companion axis variable, introduced together. A written literal length has
anonymous axes (§3.9). No term ever appears in a type. This keeps the type
system on the indexed-types side of the line (Dependent ML, GHC's
`DataKinds`), not in dependent types. Lengths come only from syntax: literal
element counts, projection positions, the literal index positions of
`contract`, `permute` and `slice` (§4.2), and the ranks of shapes (below). So
inference is Hindley-Milner plus constraint solving. Typed Core (§5.3) has one
kinded abstraction form and one kinded application form for all the kinds.

#### Dimensions

A dimension `δ` is a normalised map from atoms to non-zero integer exponents.
An atom is a base dimension or a dimension variable `d`. The base dimensions
are the seven of the SI (L, M, T, I, Θ, N, J) and plane angle, whose base unit
is the radian (§3.2.11). `1` is the empty map. Two dimensions are equal when
their maps are equal. Exponents are unbounded integers, never machine
integers that wrap: `:type 1 m^18446744073709551616` is `Num
(m^18446744073709551616)`.

#### Shapes and lengths

A shape is unified element-wise. Two closed shapes must have the same rank
and unify position by position, the lengths first and then the name slots. A
shape variable binds to any shape, with an occurs check. A shape variable can
only stand at the tail, so `n : s` means "rank at least one". Shape
polymorphism gives `+`, `-`, `neg` and `vmap` one type for every rank: `(+) :
Tensor s d -> Tensor s d -> Tensor s d`.

A length `ν` is a literal `k`, a variable `n`, a variable plus a literal offset
`n + k`, or `rank s + k`. The offset form exists for projection (§2.10). `t.i`
gives `t` the type `Tensor (n + i + 1 : s) d` with fresh `n` and `s`. This
says "rank at least one, first length at least `i + 1`" and nothing more, and
the result is `Tensor s d`. So `let first v = v.0` infers `forall n s d.
Tensor (n + 1 : s) d -> Tensor s d` by unification alone.

A slice along a later axis (`t._.i`, `slice k i t`, §2.10) uses the same offset
one axis further in. `t` gets `Tensor (l0 : … : lk-1 : n + i + 1 : s) d` with
fresh `l0 … lk-1`, `n` and `s`, and the result is `Tensor (l0 : … : lk-1 : s)
d`. So `\m -> m._.0` is `Tensor (n : m + 1 : s) d -> Tensor (n : s) d`.

- When the length at axis `k` is a known literal that is too small for `i`,
  the error says so in the projection's words, naming the axis:
  `[1, 2; 3, 4]._.2` is "position 2 is out of range for axis 1 of length 2".
- When the rank is known and too small, the error is the rank message of
  `contract` (§4.2), not a shape mismatch: `[1, 2, 3]._.0` is "slice 1 0
  needs a tensor of rank at least 2, got Vec 3".
- Through a polymorphic definition (`let col2 m = m._.2` applied to a 2×2
  matrix), the offset rule reports the length as too short, as it does for
  `v.2`.

Unification stays first-order:

- `n + k` against a literal `j`: if `j ≥ k`, then `n := j - k`, else fail. So
  `[1, 2].2` fails at check time with "position 2 is out of range for a
  vector of length 2".
- `n + k` against `m + j`: if `j ≥ k`, then `n := m + (j - k)`, else `m := n +
  (k - j)`.
- Literals against literals: equal, or fail. Variables bind as usual.

There is no other length arithmetic. So `cross` fixes `3`, and `inverse`
forces a square shape.

#### The rank of a shape

`rank` is the one type-level function. `rank σ` is the number of lengths in
`σ`, which is a length. It exists so that `timap` (§3.3) can type its index
as `Vec (rank s)`. It always normalises to a residual over one shape variable
plus a literal offset: `rank [] = 0`, `rank (ν : σ) = rank σ + 1`, and `rank
s` of a shape variable stays as it is. So a length is still a literal, a
variable plus an offset, or `rank s + k`. When `s` is bound, the rank is
normalised again: `rank s` with `s := (n : m : s1)` becomes `rank s1 + 2`, and
with `s := [2, 3]` the literal `2`. Unification therefore stays first-order.
Its rules for `rank` are in §4.2. It prints in parentheses where an offset
form does, `Vec (rank s)` and `Vec (rank s + 1)`. A written type cannot name
it: `rank` in a type position is refused with "rank s is a length, not a
type; write it where a length goes, as in Vec (rank s)", and `rank` cannot
name a parameter or a binder.

**Implemented in:** `Metron.Type.Base` (`Type`, `Kind`, `Len`, `Shape`, `Axis`, `rankLen`, `appendShape`), `Metron.Type` (`renderType`, `renderScheme`, `renderSignature`), `Metron.Dimension` (`dimMul`, `dimInv`, `dimPow`, `renderDim`, `renderDimIn`), `Metron.Type.Syntax` (`tyType`, `tyDim`, `tyLen`, `tyShape`, `signatureScheme`), `Metron.Infer` (`unify`, `unifyLen`, `unifyShape`, `unifyAxis`, `unifyFrame`, `unifySpace`).
**Tested by:** "types"; "dimension syntax"; "units"; "axis slots"; "spaces and frames (design §3.10, part F)"; "data".

### 4.2 Products, shape constraints and the instances

Nothing in the language is overloaded except equality and ordering. Every
product is its own operator with one type (core.md, "Operators across
ranks"):

```
(*) (⊗)  outer : Tensor s1 δ1 -> Tensor s2 δ2 -> Tensor (s1 ++ s2) (δ1·δ2)   -- tensor product; scalar scaling is the rank-zero case
(·) (@)  dot   : Tensor (s1 ++ [n]) δ1 -> Tensor (n : s2) δ2 -> Tensor (s1 ++ s2) (δ1·δ2)   -- contracting product: dot, Mat·Vec, Mat·Mat
(∧) (/\) wedge : Vec n δ1 -> Vec n δ2 -> Mat n n (δ1·δ2)                       -- antisymmetrised outer product; the general binary product of vectors
(⋆)      star  : Mat 3 3 δ -> Vec 3 δ                                          -- 3D Hodge dual
(×) (><) cross : Vec 3 δ1 -> Vec 3 δ2 -> Vec 3 (δ1·δ2)                         -- mathematically: cross a b = (ε @ b) @ a
(⊙) (.*) emul  : Tensor s δ1 -> Tensor s δ2 -> Tensor s (δ1·δ2)               -- elementwise
(⊘) (./) ediv  : Tensor s δ1 -> Tensor s δ2 -> Tensor s (δ1/δ2)
(/) (÷)  div   : Tensor s δ1 -> Num δ2 -> Tensor s (δ1/δ2)                     -- division by a scalar
```

`dot`'s contracted positions, the left's last and the right's first, are one
length and one name slot (§3.9). So contracting along different axis sets is a
type error. Division of a tensor by a tensor is `⊘`. `/` takes a scalar
divisor only, so it has one type too. `*` and `/` take amounts. Units at their
operands are elaborated as explicit amounts before inference (§3.10, U2).

#### Shape-append constraints

The types of `outer` and `dot` mention shape concatenation `s1 ++ s2`, which
is not a syntactic shape when the rank of `s1` is unknown. Inference records a
**shape-append constraint** `s3 ~ s1 ++ s2` and solves it as soon as it can:

- When `s1` is closed (it ends in `[]`), `s3` is the cons chain of `s1`'s
  lengths in front of `s2`, which the shape language expresses directly.
- When `s2` is scalar, `s3` equals `s1`, including a tensor of unknown rank.
- When `s2` and `s3` are both closed, `s1` is the prefix of `s3` of rank
  `rank s3 - rank s2`, and the remainder unifies with `s2`. A closed `s3`
  shorter than `s2` fails with "the result of a product has lower rank than
  one of its operands".
- Otherwise the constraint waits. Every step is first-order and unitary.

At a generalisation point, a constraint whose variables are all about to be
quantified cannot wait longer, and it is **defaulted**: the unknown part of
the left operand takes the least rank the constraint allows. A left operand of
unknown rank is therefore a scalar for `outer` and a vector for `dot`. So `\a b
-> a * b` is `forall d s d1. Num d -> Tensor s d1 -> Tensor s (d*d1)`, and `\k
v -> 2 * k * v` is `forall d s d1. Num d -> Tensor s d1 -> Tensor s (d1*d)`.

An operand that already has leading lengths keeps them and gains only those
the result still needs:

| Definition | `:type` |
|---|---|
| `\x -> [[x]] @ [2]` | `forall d (a : 1). Num d -> Vec a d` (`x` a scalar, `[[x]]` a matrix) |
| `\x -> [x] * [1]` | `forall d (a : 1) (b : 1). Num d -> Mat a b d` |
| `\x -> (x @ [[1, 2]]).0.1` | `forall n (a : 1) d. Mat (n + 1) a d -> Num d` (the result's two lengths make `x` a matrix) |

A default that made the whole operand a scalar or a vector refuses these,
though each checks once the rank of `x` is known. The two constraints of one
`dot` share the left's leading part, so that part takes the most lengths that
either of them needs. This is the one place the type system guesses, and it
guesses the common case.

**Open.** Dictionary passing is not built. With it, an unresolved product
constraint becomes a parameter of the definition (a dictionary) instead of a
default, and `\k v -> 2 * k * v` is polymorphic in the rank of `k` (§10).

#### Ranks

A length `rank s + k` (§4.1) unifies with another length by binding a variable
outright wherever it can. A rank says exactly how many lengths a shape has
and nothing about the lengths themselves:

- `rank s + k` against a literal `j`: if `j ≥ k`, then `s` is `j - k` fresh
  length variables, `s := [n1, …, n(j-k)]`, else fail ("a rank of at least 3
  cannot be 2"). The lengths stay unknown. Only the rank is fixed.
- `rank s + k` against `n + m`: if `k ≥ m`, then `n := rank s + (k - m)`.
  Otherwise the rank must be at least `m - k`, which a shape says by its
  leading lengths: `s := (n1 : … : n(m-k) : s1)` with fresh variables, and
  then `n := rank s1`. No length ever carries a negative offset, so "at
  least" is never lost. In `timap (\i x -> i.1 * x) t`, the projection gives
  `i : Vec (n + 2)`, and to unify that with `Vec (rank s)` makes `t : Tensor
  (n1 : n2 : s1) d`.
- `rank s + k` against `rank s + j`: the offsets must be equal.
- `rank s + k` against `rank s' + j` for another shape variable: the variable
  with the smaller offset gains the difference as leading lengths, as above.
  What remains, `rank s1 = rank s2` between two unbound variables, has no
  first-order solution. It is recorded as a pending **rank equation**, beside
  the shape-append constraints, and it is solved as soon as either shape is
  bound.

A rank equation that is still pending at a generalisation point, with all its
variables about to be quantified, is a static error: "two tensors here must
have the same rank, which a generalised type cannot say; give one of them a
known rank". Any rank is a guess, so it is not defaulted. A dropped equation leaves
nothing in the scheme to make a use site check it, so it is not dropped. It
arises when one index function is shared by two maps of unknown shapes, as in
`\f t u -> (timap f t, timap f u)`.

Everything else about a rank is in the type itself, so a definition over
`timap` generalises with no constraint. `\t -> timap (\i x -> i.0 * x) t` is
`forall n s d. Tensor (n : s) d -> Tensor (n : s) d`. `\t -> timap (\i x ->
dot i i * x) t`, whose index function works at any length, is `forall s d.
Tensor s d -> Tensor s d`. Lint checks a use of `timap` as it checks any fixed
scheme: the recorded type, with the rank normalised, must be an instance of
`timap`'s scheme, so the index length must be the rank of the recorded shape.

#### Equality and ordering

Equality is overloaded. `==` and `/=` take two values of one type `τ` and emit
an **instance constraint** `Eq τ`. Its instances are:

- tensors of any shape (`Tensor s d`).
- points (`Point c`) and amounts on a frame (`Diff c`).
- a declared type `T τ…` when every field of every constructor, at those
  arguments, has equality.

`Bool`, tuples and lists are declared types (§4.1). So `Bool` has equality
outright, a tuple has it when every component does, and a list has it when its
element does, by the same rule. Values of data types are equal when their
constructors are the same and their fields are pairwise equal. For a declared
type, the instance is derived structurally. A recursive occurrence of `T` in
its own fields is the instance being derived (coinductively). Which of `T`'s
parameters need equality is a least fixed point over the fields. So `Eq (Tree
τ)` reduces to `Eq τ`, `Eq Shape` holds outright, and a nested type such as
`data N a = Z a | S (N (a, a))` is decided without unfolding.

The ordering operators `<`, `<=`, `>`, `>=` emit an `Ord τ` constraint. Its
instances are numbers (`Num d`) and points on a space of numbers (`Point
degC`). A tensor has no order: anything else is refused with "no ordering on
…; only numbers and points compare".

Both constraints are solved the same way. As soon as `τ` is known, it is
checked. At generalisation an unresolved `τ` defaults to `Num`. Any other type
is a static error: "no equality on a -> a" for `(\x -> x) == (\x -> x)`. A
declared type with a function field has no equality. Lint re-checks every
solved constraint on the elaborated term, so a primitive is never evaluated at
a type that its implementation cannot handle (core.md §9).

#### Contraction, permutation and slicing with literal positions

`contract i j`, `permute [p0, …, pk-1]` and `slice k i` work at any rank. Their
positions are part of the type, as a projection's position is (§4.1). So the
desugarer insists on literals, as it does for an exponent:

- Each index of `contract` is a literal natural, and the two are distinct.
- `permute`'s argument is a literal vector that is a permutation of `0 ..
  k-1` with `k ≥ 1`.
- The axis `k` and the position `i` of `slice` are literal naturals.

Anything else is a desugaring error that quotes the rule: "the positions of
contract must be literal natural numbers: contract i j t", "contract pairs two
different positions, not position 0 with itself", "permute [0, 0] is not a
permutation of 0 .. 1", "permute takes a literal vector of natural numbers, a
permutation of 0 .. k-1 with k ≥ 1", "the axis and position of slice must be
literal natural numbers: slice k i t". A bare `contract`, `permute` or `slice`
without its positions is the same kind of error. To leave off only the tensor
is an ordinary eta expansion: `contract 0 1` alone is `\x -> contract 0 1 x`.
The positions stay arguments of the primitive, constants in Core, so no Core
form is needed (core.md §5).

The scheme is computed from the literals, with fresh variables at each use,
and is then an ordinary first-order scheme. With `a = min i j` and `b = max i
j`:

```
contract i j          : Num -> Num -> Tensor (l0 : … : lb : s) d -> Tensor (l0 : … : lb without positions a and b : s) d
                        where lb is the variable la: the paired lengths are one length, and their axes one slot
permute [p0, …, pk-1] : Vec k -> Tensor (l0 : … : lk-1 : s) d -> Tensor (lp0 : … : lpk-1 : s) d
slice k i             : Num -> Num -> Tensor (l0 : … : lk-1 : n + i + 1 : s) d -> Tensor (l0 : … : lk-1 : s) d
```

The leading `Num` and `Vec k` are the literal positions themselves. Because
the paired positions of `contract` share one length variable, unequal lengths
are an ordinary length-unification failure: `contract 0 1 [[1, 2, 3], [4, 5,
6]]` reports "expected Tensor (n : n : s) d, got Mat 2 3: lengths differ: 2
and 3". A tensor whose rank is known and too small for the positions is
reported as such, not as the shape mismatch beneath it: `contract 0 2` on a
matrix is "contract 0 2 needs a tensor of rank at least 3, got Mat 2 2", and
`permute [2, 0, 1]` on a matrix is "permute [2, 0, 1] needs a tensor of rank
at least 3, got Mat 2 2". When the rank is not yet known, the scheme asks for
at least `b + 1` (or `k`) positions, and a later use that cannot supply them
fails with the shape mismatch. So positions beyond the rank are always type
errors, never run-time errors. Lint recomputes the scheme from the `TLit`
arguments of the elaborated `TPrimApp` and checks that the recorded type is an
instance of it, as it does for every fixed scheme.

**Implemented in:** `Metron.Infer` (`primType`, `solveOne`, `solvePending`, `defaultProducts`, `generalise`), `Metron.Primitive.Types` (`primScheme`, `primSchemeFor`), `Metron.Desugar` (`indexedForm`, `indexProblem`), `Metron.Type` (`equalityArgs`), `Metron.TCore` (`lintConstrained`, `equatable`).
**Tested by:** "types"; "products"; "contraction and permutation"; "slicing along an axis"; "soundness"; "properties" › "replayed seeds".

### 4.3 Types of the primitives

Every primitive has one scheme, checked by inference and again by lint, and
listed in `Metron.Primitive.Types.primScheme`. `outer`, `dot`, the equality
and the ordering operators have the relational types of §4.2. The scalar
domain of the backend (§8.2) does not change a scheme. Units are syntax
(§3.10, part U): the internal primitives `to`, `scale` and `unit` take a
`Unit δ`, which describes Core, not a type that a user can write.

```
a number literal : Num                      -- of any shape for a constant tensor
m kg s A K mol cd rad : Unit B              -- the base units are units (3.10, U1)
(+) (-)     : Tensor s d -> Tensor s d -> Tensor s d
neg abs     : Tensor s d -> Tensor s d
(== /=)     : a -> a -> Bool                -- Eq a (4.2)
(< <= > >=) : a -> a -> Bool                -- Ord a: numbers and points on a space of numbers (4.2)
(&& ||)     : Bool -> Bool -> Bool          not : Bool -> Bool
to          : Tensor s d -> Unit d -> Tensor s d         -- a display unit (3.2.12, 3.10 U6); toChart and toAxes for a chart, below
scale       : Tensor s 1 -> Unit d -> Tensor s d         -- the quantity rule after a unit: 3 km, [1, 0, 0] (km/h) (2.6, 3.10 U4)
unit        : Num d -> Unit d                            -- internal unit construction (3.10 U7)
normal uniform : Num d -> Num d -> Distribution d
sample         : Distribution d -> Num d
sqrt        : Num (d^2) -> Num d
floor ceil round : Num -> Num
sin cos tan : Num rad -> Num
asin acos atan : Num -> Num rad
sinh cosh tanh exp log : Num -> Num
atan2       : Num d -> Num d -> Num rad
pi          : Num
e ^ n       : Num d -> Num (d^n)            -- a special form: n an integer literal
v.i         : Tensor (n + i + 1 : s) d -> Tensor s d   -- a special form: i a literal position (2.10, 4.1)
mid sd      : Tensor s d -> Tensor s d       -- empirical input statistics
nextUp      : Tensor s d -> Tensor s d   -- the double backend's (8.2)
ulps        : Num d -> Num d -> Num         eps : Num
fma         : Num d1 -> Num d2 -> Num (d1*d2) -> Num (d1*d2)
isNaN isInfinite : Num d -> Bool
norm        : Vec n·a d -> Num d
transpose   : Mat n·a m·b d -> Mat m·b n·a d
inverse     : Mat n·a n·b d -> Mat n·b n·a (1/d)
det         : Mat n·a n·b -> Num                        -- dimensionless only, any n (4.6)
cholesky    : Mat n·a n·b (d^2) -> Mat n·a n·b d
covariance  : Vec n·a d -> Mat n·a n·a (d^2)            -- empirical covariance of input realizations (3.5)
crossCovariance : Vec n·a d1 -> Vec m·b d2 -> Mat n·a m·b (d1*d2)   -- over paired input realizations (3.5, 3.7)
expm        : Mat n·a n·a -> Mat n·a n·a                -- the matrix exponential, dimensionless (3.3)
transformBy : Mat n·_ n·_ -> Tensor s d -> Tensor s d   -- R along every axis; every length of s must be n, checked at run time; anonymous axes (3.3, 3.9)
vmap        : (Num d1 -> Num d2) -> Tensor s d1 -> Tensor s d2
vzipWith    : (Num d1 -> Num d2 -> Num d3) -> Tensor s d1 -> Tensor s d2 -> Tensor s d3   -- per pair of components; no display unit (3.3)
indices     : Vec n·a d -> Vec n·a                      -- [0, 1, …, n-1], exact; the components are not read
timap       : (Vec (rank s) -> Num d1 -> Num d2) -> Tensor s d1 -> Tensor s d2   -- the multi-index, exact and anonymous, then the component (3.3, 4.1)
seq         : a -> b -> b                               -- evaluate the first, then give the second (7.7)
contract i j t, permute [p…] t, slice k i t             -- special forms with literal positions (4.2)
mkRoot      : Frame F -> {Axes A} -> Space S -> {Unit d} -> {Tensor σ d} -> {Mat n n} -> {Vec 3 (rad/s)} -> Chart F   -- a chart on a space (3.10, F10)
mkChart     : {Frame F} -> {Axes A} -> Chart p -> {Unit d} -> {Diff p} -> {Mat n n} -> {Vec 3 (rad/s)} -> Chart F'   -- a chart on a chart: F' is F if minted, else p's (3.10, F3)
pointOn     : Chart c -> Coords c -> Point c            -- what the quantity rule builds for 20 degC (3.10, F5)
pointAdd    : Point c -> Diff c -> Point c              -- .+
pointSub    : Point c -> Point c -> Diff c              -- .-
pointAt     : Chart c -> Diff c -> Point c              -- an amount from the chart's origin along its axes (7.7)
toChart     : Point c -> Chart c1 -> Point c1           -- p to c1, c and c1 frames of one space (3.10, F5)
fromTo      : Point c -> Chart c -> Chart c1 -> Point c1   -- p from c to c1 (3.10, F7)
toAxes      : Tensor (n·S : t) d -> Chart c -> Tensor (n·c : t) d     -- v to c, v along the space's base axes (3.10, F10)
axesFromTo  : Tensor (n·c : t) d -> Chart c -> Chart c1 -> Tensor (n·c1 : t) d   -- v from c to c1 (3.10, F10)
p.i         : Point c -> Num δ                          -- a coordinate, the step applied; δ the space's dimension (3.10, F5)
rotationOf  : Chart c -> Mat S c                        -- rows along the space's base axes, columns along the frame's (3.8)
spinOf      : Chart c -> Vec S (1/s)                    -- the absolute angular velocity, base axes (3.8)
originVelocityOf : Chart c -> Vec S (δ/s)               -- the velocity of the origin, base axes (3.8)
originOf    : Chart c -> Vec S δ                        -- the origin from the space's base origin, base axes (3.8)
withAxes    : Chart c -> Vec n·_ d1 -> Vec c d1         -- anonymous axes read as the chart's; no arithmetic (3.9)
```

Each length in these types is a position with a name slot (§3.9). The table
writes `n·a` where the slot matters (this is not syntax) and otherwise the
length alone. A length variable has an axis variable beside it, and so does a
literal `3` of the three-dimensional primitives. The slots are shared where
the axes are one set. `_` is anonymous, and `S` stands for the frame's space's
base axes. `Frame F`, `Axes A` and `Space S` are the types of the
constructors that a chart or space declaration mints (§3.10, F3). The chart
primitives read `F`, `A` and `S` off those arguments, as `contract` reads its
positions. A frame's space, shape and dimension are its companions (§4.1), so
`δ` above is the space's dimension, solved once the frame is known. Which
slots are shared is listed in §3.9, and the frame companions in §3.10, part F.

The circular functions take an angle and their inverses return one
(§3.2.11). `rad` is a base unit and `deg = pi / 180 * 1 rad`, so `sin (90
deg)` type-checks and `sin (1 m)` and `sin 1` fail with "sin takes an angle:
write 1 rad or 45 deg: expected Num rad, got Num m: dimensions differ by
rad/m". `atan2` accepts any one dimension for its two arguments. The
hyperbolic functions, `exp` and `log` take plain numbers.

Distribution constructors take deterministic scalar parameters of matching
dimension. `sample` returns a number of that dimension (§3.2.5).

`transformBy` is the one primitive with a run-time shape check. Its argument
can have any rank, but every length must be the matrix's `n`: a shape `[n, n,
…, n]` of unknown rank, which the shape language cannot write (a shape is a
list of lengths with a variable tail, §4.1). So its type is `Mat n n -> Tensor
s d -> Tensor s d`, and the evaluator refuses another length: "transformBy:
every axis must have length n: the matrix is 3 × 3 and the tensor's lengths
are [3, 2]". **Open.** A shape language that can say "every length is `n`" makes this
a type error (§11).

**Implemented in:** `Metron.Primitive.Types` (`primScheme`, `primSchemeFor`, `primSchemeForLits`), `Metron.Primitive` (`primArity`, `baseUnit`, `typedPrims`), `Metron.Infer` (`primType`, `infer`), `Metron.TCore` (`lintConstrained`).
**Tested by:** "types"; "soundness"; "typed core"; "lint regressions"; "rotations"; "internal units and public amount arithmetic".

### 4.4 Dimension unification

To unify `δ₁` with `δ₂`, solve `δ = δ₁·δ₂⁻¹ = 1`. Write `δ` as `d₁^x₁ ⋯ dₘ^xₘ ·
B₁^y₁ ⋯ Bₙ^yₙ`, with `|x₁|` the smallest variable exponent. Its sign does not
matter, since `δ = 1` and `δ⁻¹ = 1` are the same equation.

1. **No variables** (`m = 0`): succeed if all `yⱼ = 0`, else fail with
   "dimensions differ by δ".
2. **One variable** (`m = 1`): if `x₁` divides every `yⱼ`, substitute `d₁ :=
   ∏ Bⱼ^(-yⱼ/x₁)`. Otherwise fail: there is no integer solution.
3. **Several variables**: if `x₁` divides every other `xᵢ` and every `yⱼ`,
   substitute `d₁ := ∏ dᵢ^(-xᵢ/x₁) · ∏ Bⱼ^(-yⱼ/x₁)` and succeed. If `x₁`
   divides every other `xᵢ` but not every `yⱼ`, fail: there is no integer
   solution. Otherwise substitute `d₁ := d₁' · ∏ dᵢ^(-⌊xᵢ/x₁⌋) · ∏
   Bⱼ^(-⌊yⱼ/x₁⌋)` with a fresh `d₁'`, and repeat on the result. The
   exponents shrink as in Euclid's algorithm, so this terminates.

The problem is unitary: when a unifier exists, there is a single most general
one.

Worked example: `sqrt (x * x)` with `x : Num d₁`. `x * x : Num (d₁^2)`, and
`sqrt` expects `Num (d^2)`. Unify `d^2` with `d₁^2`: `δ = d^2 · d₁^-2`. The
smallest exponent is 2 (a tie: pick `d`). 2 divides -2, so `d := d₁`, and
`sqrt (x * x) : Num d₁`.

An example that needs the Euclid step: unify `d₁^2 · d₂^3` with `1`. The
smallest is `x₁ = 2` on `d₁`, and 2 does not divide 3. Substitute `d₁ := d₁' ·
d₂^(-⌊3/2⌋) = d₁' · d₂^-1`. Now `δ = d₁'^2 · d₂^-2 · d₂^3 = d₁'^2 · d₂`. The
smallest is 1 on `d₂`, which divides 2, so `d₂ := d₁'^-2`. Composed: `d₂ =
d₁'^-2` and `d₁ = d₁'^3`. Check: `d₁'^6 · d₁'^-6 = 1`. These are exactly the
solutions of `2a + 3b = 0`.

A non-unifiable example: `Num m` with `Num s`. `δ = L · T^-1` has no variables
and is not empty, so `1 m + 4.5 s` is rejected with "expected Num m, got Num s:
dimensions differ by m/s". A dimension equation with no integer solution, such
as `sqrt` of a dimension that is not a square, is a type error and never a
loop.

**Implemented in:** `Metron.Infer` (`unifyDim`, `bindVar`, `unifyDimensions`), `Metron.Dimension` (`dimDiv`, `dimInv`, `dimAtoms`, `dimFromAtoms`).
**Tested by:** "units"; "types"; "properties" › "the dimension unifier: a solution solves, a refusal has none (design §4.4)".

### 4.5 Inference

Inference is algorithm W over Core (§5.1). It uses §4.4 for dimensions,
emits the §4.2 constraints at the products and the overloaded operators, and
elaborates to Typed Core in the same pass (§5.3). A binding group is split
into strongly connected components (§6.3). Each component is inferred
monomorphically and then generalised over its free variables of every kind.
Printed schemes are headed by `forall` and their variables (§4.8). They use
`a b c` for type variables, `n m k` for lengths, `s s1` for shapes and `d d1`
for dimensions, and show dimensions with base-unit symbols:

```
> :type \r -> pi * r^2
forall d. Num d -> Num (d^2)
> :type \a b -> a * b
forall d s d1. Num d -> Tensor s d1 -> Tensor s (d*d1)
> :type 9.81 m/s^2
Num (m/s^2)
```

Inference is deterministic: the same input gives the same scheme, variable
names included.

**Implemented in:** `Metron.Infer` (`elaborateClosed`, `elaborateClosedWith`, `infer`, `generalise`, `generaliseAll`, `instantiate`), `Metron.Resolve` (`processGroup`, `enterComponent`).
**Tested by:** "types"; "properties" › "typed programs"; "properties" › "blind programs".

### 4.6 Known limitations

- A signature (§4.8) is checked after inference and is not used during it.
  So there is no polymorphic recursion: inside a cycle, a member's recursive
  uses see its one monomorphic type, whatever its signature says, and a
  definition that needs its own signature to check does not check. The one
  exception is a reading (§3.10, U4, U6). A quantity or a `to` whose reading
  the types choose is first inferred with the definition's signature as an
  ascription of its body. The reading found is written into the term, which is
  then inferred alone as usual (`pt c = 3 c` stores `pointOn c 3`). The
  definition's own ascriptions do not take part, since they are not in its
  term.
- `^` requires a literal exponent, because `x ^ y` with a run-time `y` has no
  static dimension. `x ^ y` is a parse error ("unexpected y, expecting - or
  integer literal"). `sqrt` covers the `1/2` case.
- `det` is on dimensionless matrices only. Its natural type, `Mat n n d -> Num
  (d^n)`, needs a length as a dimension exponent, which the type system does
  not have. So `det : Mat n n 1 -> Num 1`, and `:type det` prints `forall n a.
  Mat n a -> Num`. It is polymorphic in `n` with no static size check, so `let
  d a = det a` generalises and works at every size. A matrix with a unit is a
  type error: `det ([[1, 0], [0, 1]] m)` is "expected Mat n n, got Mat 2 2 m:
  dimensions differ by 1/m". Divide the unit out first, as in `det (a / (1
  m))`, and multiply by `m^n` for the size at hand.
- Dimension polymorphism is let-polymorphism.
- `rank` is the only type-level function. A type cannot say that two unknown
  shapes have the same rank, so a definition that needs that, such as `\f t u
  -> (timap f t, timap f u)`, is refused at generalisation (§4.2).
- Vectors and matrices are homogeneous in dimension (§3.3). A matrix of mixed
  dimensions is written as blocks (§3.7).
- Component access needs a literal position (§2.10). Computed indices do not
  exist. The same holds for the positions of `contract`, `permute` and
  `slice` (§4.2): a function cannot take them as parameters, so `\i ->
  contract i 0 t` is an error.
- A pending relation between `Diff c` and a tensor of unknown shape cannot be
  carried by a generalised scheme. It is refused with "the amount between
  points on a frame of a space not known here: give a signature naming the
  space, as in forall (c : GCRS)". Give a signature that names the space or
  constrains its amounts, as in `(s : Space (Vec 3 m)) (c : s)` (§3.10, F4).

**Implemented in:** `Metron.Infer` (`generalise`, `quantify`, `settleReadings`), `Metron.Resolve` (`withReadings`), `Metron.Primitive.Types` (`primScheme`).
**Tested by:** "units"; "display units"; "spaces and frames (design §3.10, part F)"; "turnedCharts"; "movingCharts"; "standard library".

### 4.7 Error reporting

**What is static.** A binding group is parsed, desugared, inferred and
elaborated as a whole. Nothing in it is stored or evaluated unless all of that
succeeds. The one-shot CLI checks a whole file first. Every error below is
reported at that point, before any arithmetic runs:

| Expression | Error | Found by |
|---|---|---|
| `1 m + 4.5 s` | "expected Num m, got Num s: dimensions differ by m/s" | dimension unifier, §4.4 |
| `[1, 2] + [1, 2, 3]` | "expected Vec 2, got Vec 3: lengths differ: 2 and 3" | length unification, §4.1 |
| `[1, 2].2` | "position 2 is out of range for a vector of length 2" | length unification, §4.1 |
| `1 + true` | "expected Num, got Bool" | unification |
| `sin (1 m)` | "sin takes an angle: write 1 rad or 45 deg: expected Num rad, got Num m: dimensions differ by rad/m" | dimension unifier |
| `[[1, 0], [0, 1]] @ [1, 2, 3]` | "lengths differ: 2 and 3" | shape-append constraint, §4.2 |
| `if 1 then 2 else 3` | "cannot match Num against the constructor False: the condition of `if` must be a Bool" | unification |
| `x ^ y` with a non-literal `y` | a parse error: the exponent must be an integer literal | parser |
| `det a` with `a : Mat 2 2 m` | "expected Mat n n, got Mat 2 2 m: dimensions differ by 1/m" | dimension unifier |
| `foo + 1` with no `foo` in scope | "unknown name `foo`" | desugaring |
| `let bad = 1 + true` | the message names the definition: "in `bad`" | unification |

`1 + 4.5` is not an error: both are exact rationals of type `Num`. There is
no `Int` versus `Double` distinction anywhere in the language.

**What remains dynamic.** Only value-dependent failures survive to run time:
rational division by zero, `sqrt` or `log` of a
range that reaches zero or below, an undecidable comparison, `inverse` of a
singular rational matrix, `transformBy` of a tensor with another length
(§4.3), a chart whose step is not invertible (§3.6), a resource limit (§8.1),
and non-termination. None of these is a type error, and the type system
cannot remove them without dependent types.

**Provenance.** Core has no source positions, because they change the
hash. The desugarer returns the Core term together with a *provenance table*:
a map from a path into the term (the sequence of child positions from the
root) to the surface span that produced that node, as a source map does. The
table also carries *hints*: advice that the desugarer attaches to a span while
it still sees the syntax, printed under a type error that lands there. A
literal argument followed by a unit name (`Rect 3 m 4 m`) is two arguments,
and the hint says "3 and `m` are two separate arguments here; a quantity in
argument position needs parentheses: (3 m)" (§2.6). A name that ends a
quantity gets "`u` is not a declared unit, so the quantity ends before it; if
it is a unit, write 9.81 (m/u)" (§3.10, U5). A unit where an amount goes is
refused with the message of §3.10, U3.

- Inference tracks the current path as it walks the term, and every
  constraint it emits records the path of the node that made it. A failed
  unification therefore carries the expected and actual types and a path,
  which the table turns into a span.
- The dimension unifier reports the residual it cannot cancel, the length
  unifier the two lengths, and the instance solver the constraint it cannot
  satisfy. So messages name what the user wrote:

  ```
  error at 1:7
    1 m + 4.5 s
          ^^^^^
    expected Num m, got Num s: dimensions differ by m/s
  ```

- A definition in the codebase has no source text. A type error at a use of
  one points at the use's span.

The provenance table lives for one REPL interaction or one file. It is never
stored, so hashes and the codebase are unaffected. The evaluator's type-error
cases are unreachable for linted terms and are reported as internal errors.

**Open.** Run-time errors print without a location ("error: division by
zero"). The design intends a failing `PrimApp` to report its path, so that the
message points at the operation, and an error that involves a stored
reference to name the definition and its stored type (`period : Num m -> Num
s`). Neither is built (§10). The provenance paths and the paths inference
walks disagree inside `case` alternatives, `if` branches and list literals
(§11).

**Implemented in:** `Metron.Desugar` (`desugarClosed`, `desugarDefinition`, `provenanceAt`, `quantityHints`, `renderDesugarError`), `Metron.Infer` (`failAt`, `unify`), `Metron.Compile` (`checkExpr`, `renderResolveErrorWith`, `renderEvalError`), `Metron.Syntax` (`renderSpanError`).
**Tested by:** "types"; "desugar"; "end to end"; "units are syntax".

### 4.8 Type annotations

A **signature** `name :: type` (§2.2) says what type a definition must have.
The type is written as `:type` prints types (§4.1), in the scope of the
statement.

**Decided.** The variables of a signature are bound by `forall`: `ident ::
forall a. a -> a`, `norm2 :: forall n d. Vec n d -> Num (d^2)`, with `∀` for
`forall`. Every other name in it is a name and resolves like one: a built-in
type, a declared type, a base unit or a unit, by the scope. So a new unit
called `d` cannot change the meaning of an existing signature. An unknown
lowercase name is an error, not a guessed variable:

```
f :: a -> a
error at 1:6
  f :: a -> a
       ^
  unknown name `a` in a type; bind it with forall if it is a variable
```

An unknown capitalised name is an unknown type. A type without variables needs
no `forall`: `area :: Shape -> Num (m^2)`.

- **Kinds come from use**, as a `data` parameter's kinds do (§2.3). `a` in `a
  -> a` is a type, `n` in `Vec n` a length, `s` in `Tensor s d` a shape, and
  `d` a dimension. A variable used at two kinds is refused. A length variable
  stands for a whole axis set: its length and a companion axis variable
  (§3.9). A binder that is not used binds nothing.
- **A sized binder**, `forall (a : 3) d. Vec a d -> Vec a d`, is a length
  fixed to the literal, beside axes of its own: "any three-axis set, the same
  one throughout". It accepts a `Vec 3` of any axes and refuses a `Vec 2` with
  the lengths message ("expected Vec 3 d, got Vec 2: lengths differ: 3 and
  2"). A definition that holds of it must be polymorphic in those axes (`let
  keep v = v` is). Used as anything but a length, it is refused. A binder can
  also name a frame's space, `(c : ITS90)`, or constrain a space's amounts,
  `(s : Space (Vec 3 m))` (§3.10, F1).
- **A binder shadows** a unit, a base unit or a declared type of its name
  throughout its type, brackets included. For a signature given with its
  definition, it also shadows in the types of that body's ascriptions
  (below). It never shadows in an expression. In `same :: forall s d. Tensor
  s d -> Tensor s d`, `s` is the shape variable. In `secs :: Num s -> Num s`,
  it is the second. In `forall s. Num s -> Num s`, it is a dimension
  variable, and the body of either definition still reads `1 s` as the
  second. A binder is a lowercase name other than `rank`, bound once, so only
  a lowercase declared type can be shadowed. A binder used as a head, `a
  Num`, is refused as taking no arguments ("parameter `a` takes no
  arguments").
- `forall` goes only at the head of a signature's or an ascription's type.
  `data` parameters are already explicit, and a field cannot hold a `forall`.

**Printing.** `:type`, `:ls` (definitions and constructors), and every place a
signature is written back (`:edit`, `:export`, `:scratch`'s `pending:` line
and the `sig` log line, §7.4) print the `forall` when the type has variables,
in the order the printer names them. So what is printed can be pasted back:
`forall a. a -> a`, `forall n d. Vec n d -> Num d`. A type without variables
prints without one. Variables are named by kind (`a b c`, `n m k`, `s s1`, `d
d1`). Since a binder shadows a unit of its name, a name is skipped only when
the same type prints that base symbol in a dimension. So a shape variable
beside the second is `s1`: `forall s1 d. Tensor s1 d -> Tensor s1 (s*d)`.
Axis variables print as nothing and are not bound, except beside a sized
binder, which prints sized: `keep :: forall (a : 3) d. Vec a d -> Vec a d`
(§3.9). Error messages, `:lint` and `:core` print types without `forall`.
`forall` prints so in unicode mode too: `∀` is input only.

**Queries stay implicit.** A `:ls : type` query is a search pattern, not a
type to read back, so its unknown lowercase names are variables (`:ls : {a} ->
Num` finds `length`). A query headed by `forall` reads as a signature does,
and so does a `sig` log line.

**Meaning: an instance of the inferred scheme.** A signature is checked after
the definition's component is inferred and linted, and is never used while
inferring it. It holds when its type, with its own variables held fixed as if
they were constants, is an instance of the inferred scheme. That is, there is
a substitution of the *inferred* scheme's variables that gives the signature's
type (`Metron.Type.Match.signatureHolds`: one-way matching of each kind, the
same matching lint uses for type applications). So a signature can narrow a
definition's type and never widen it:

```
f :: Num m -> Num m
let f x = x                     -- holds: a := Num m

g :: forall a. a -> a
let g x = 1                     -- refused, at the signature:
error at 1:1
  g :: forall a. a -> a
  ^^^^^^^^^^^^^^^^^^^^^
  `g`'s definition has type `a -> Num`, not as general as its signature `a -> a`
```

**Label-level.** A signature belongs to the name, not to the hash. It is kept
beside the names, as the `unit` and `chart` flags are (§3.2.12,
`Codebase.signatures`). It never changes a term's hash, and two names of one
hash can carry different signatures, one signed and one not.

- `:type f`, `:ls` and `:edit` show the signature of a signed name. An
  unsigned name shows its definition's own type.
- A later input that redefines a signed name is checked against the stored
  signature and refused with the same message at the redefinition, unless the
  same input gives a new signature.
- A propagation (§7.5) does not move a signed name to a version that its
  signature does not hold of. The name stays on its version, with the reason.
- `:rename` and `:move` take the signature with the name. `:alias` does not
  copy it, because an alias is the hash, unsigned. `:unname` removes it.
- A signature for a stored definition can be given alone, `f :: Num m -> Num
  m`, and `:add` reports `signed f`. A signature with no definition in the
  input, the scratch or the codebase is refused at `:add`: "`f9` has a
  signature but no definition; define it, or :forget f9".
- A signature names declared types by hash. When `:rename` re-hashes a type
  (§7.2) or `:edit` replaces one (§7.3), a signature that names it follows to
  the new type, unless its definition was left on the old one.

**Uses see the signature.** A reference written under a signed name, while
the name still points at that hash, is typed by the signature. Inference
instantiates the hash's own scheme, which is what the type applications in
Typed Core record and lint checks. It then instantiates the signature and
unifies the two, which always succeeds, since the signature is an instance.
With `h :: Num m -> Num m` and `let h x = x`, `h (3 s)` is refused with
"expected Num m, got Num s: dimensions differ by m/s", while an unsigned name
of the same hash takes `3 s`.

A definition's stored types and Typed Core are always those of its Core
alone. The store recomputes them from the terms on load (§7.4), before the
labels are replayed, and two definitions that differ only in the names they
were written with are one hash. So a definition that uses a signed name is
checked twice: inferred and stored as usual, then checked again with the
signatures that its references see, which can refuse it. Its own type stays
its Core's: `let h2 y = h y` has type `forall a. a -> a`, and `h2 (3 s)` is
`3 s`. To narrow `h2`, sign it. A signature is checked against the type that
the second check inferred, `Num m -> Num m` here, so `h2 :: Num m -> Num m`
holds and `h2 :: forall a. a -> a` is refused. **Open.** Whether such a
definition gets the narrower type is an owner question (§11).

**Ascription.** `(e :: type)`, anywhere an expression goes, in parentheses as
a tuple or a section is, gives `e` a type. The type is converted in the scope
of the expression as a signature's is. Its variables are bound by its own
`forall`, or by the signature of the definition it is in (below), and an
unknown lowercase name is the same error. Each of its own variables is fresh,
and the type is unified with `e`'s inferred type at `e`'s node. So an
ascription narrows and never widens:

- `(1 :: forall a. a)` is `1`, of type `Num`, because `a` is a fresh variable
  that unifies with `Num`;
- `:type \x -> (x :: forall d. Num d)` is `forall d. Num d -> Num d`, where
  `\x -> x` is `forall a. a -> a`;
- `(3 m :: Num m)` is `3 m`.

Two ascriptions whose own `forall`s both bind `d` do not share it. A failure is
reported at the ascription, in the usual form, with the prefix "the
ascription":

```
> (3 m :: Num kg)
error at 1:1
  (3 m :: Num kg)
  ^^^^^^^^^^^^^^^
  the ascription: expected Num kg, got Num m: dimensions differ by kg/m
```

An ascription does not reach Core. The desugarer puts `e` in its place, and
the term it builds is the one that is hashed, stored and run. It only notes
the written type beside the provenance (`Provenance.ascriptions`). When there
is an ascription, the input is desugared a second time for checking alone
(`Desugar.desugarMarked`). There, each ascription is a marker around `e`: a
primitive application under a reserved name that the user cannot write.
Inference reads the marker by its name, takes the converted type from the
annotations (`Infer.Annotations`, beside the signatures), unifies, and
elaborates the marker to `e`'s own typed term, so no marker reaches Typed
Core. A marker identifies the node itself, which a path into the term does
not do (§4.7, the open path mismatch). An error in the ascription is recorded
under a key of its own and so always points at it.

So `:view` and `:core` have nothing to show for an ascription: `let f x = (x ::
Num m) + 1 m` views as `f = \x -> x + 1 m`. An expression's type is narrowed
(`:type`, and what it evaluates to). Inside a definition, an ascription only
checks: the definition's type is its Core's, as for a use of a signed name
above, because the store recomputes types from the terms, which have no
ascriptions. `let gg x = (x :: Num m)` is `forall a. a -> a`, the same hash as
`let gg x = x`. Sign `gg` to narrow it.

**Scoped variables.** A signature's `forall` scopes its variables over the
body of its definition, when the signature is given in the same input as the
definition. A stored signature keeps no names, so a redefinition alone does
not see them. An ascription in the body can name them, and they are the
signature's variables, not fresh ones. An ascription's own `forall` shadows
one of the same name.

```
f :: forall a. a -> a
let f x = (x :: a)                    -- holds: x has the signature's a

g :: forall a b. a -> b -> a
let g x y = (x :: b)                  -- refused, at the signature:
  `g`'s definition has type `a -> a -> a`, not as general as its signature `a -> b -> a`
```

If `b` were a fresh variable, `(x :: b)` only narrows `x`, which any type
does, and `g` holds. Because `b` is the signature's variable, the check in which ascriptions take part (above)
wraps the definition's body in a marker for the signature itself
(`Desugar.signatureMarker`). The marker unifies the body's type with the
signature's. The ascriptions' converted types refer to the same variables,
renumbered into a range of the member's own that no variable of inference
meets (`Resolve.scopedSignature`). These unify as any variable does. The
signature is then checked, as always, against the scheme that this check
gives. So an ascription that narrowed one of its variables, or made two of
them one, is refused with the usual "not as general" message at the
signature. This happens only when an ascription names one of the signature's
variables, so a definition without one checks the same with or without the scope.
It applies to each member of a cycle with its own signature. A failure to
unify the body with the signature in that check is reported with the prefix
"the signature".

**Implemented in:** `Metron.Type.Match` (`signatureHolds`, `isInstanceOf`), `Metron.Type.Syntax` (`signatureScheme`, `explicitScheme`, `queryScheme`, `renumberBound`), `Metron.Resolve` (`checkSignature`, `usesSignatures`, `annotationsFor`, `scopedSignature`, `signMembers`), `Metron.Desugar` (`desugarMarked`, `ascriptionMarker`, `signatureMarker`), `Metron.Infer` (`Annotations`, `elaborateClosedWith`), `Metron.Codebase` (`signatureOf`, `setSignature`, `dropSignature`), `Metron.Type` (`renderSignature`).
**Tested by:** "type annotations"; "forall"; "store"; ":edit, the editor round trip".

---

## 5. Core and Typed Core

[core.md](core.md) is the companion document for this chapter. It holds the
purpose of Core, the minimality principle, the reason for each constructor,
the invariants that lint enforces, and the test that any change to Core must
pass. This chapter states what Core and Typed Core are. It does not repeat
core.md's reasons.

### 5.1 Core: the desugared language

Core is the output of desugaring and name resolution (§2.9). It is an
abstract binding tree with de Bruijn indices. Binders carry a *name hint* for
printing, and hashing, equality and substitution ignore the hints. Core is
untyped, and it is what gets hashed.

Core is **well-scoped**. The term type is indexed by the number of variables
in scope, `Term n`. A variable is a `Fin n`, and a binder's body has type
`Term (S n)`. A term with a dangling variable is a Haskell type error, not a
run-time one, and the evaluator's environment is a length-indexed vector, so
lookup is total. Core is *not* indexed by object-language type: it is the
input to the type checker, so it must hold ill-typed terms.

```
Term n ::= Var (Fin n)                -- bound variable
         | Ref hash [idx] hint        -- another definition by content hash, a cycle index, and the name written
         | PrimApp name [Term n]      -- saturated primitive application
         | Lit (Tensor shape [Rational])   -- a constant tensor: shape and flat row-major values
         | Lam hint (Term (S n))      -- one parameter
         | App (Term n) (Term n)
         | Let hint (Term n) (Term (S n))   -- non-recursive, generalising local binding
         | Con con [Term n]           -- a saturated data constructor
         | Case (Term n) [Alt n]      -- one alternative per constructor, canonical order, lazy in the bodies
         | Pow (Term n) Integer       -- e ^ n
         | Sample Label (Term n)      -- a labelled input distribution
         | Pack [Term n]              -- [a, b, c]: stack k tensors of shape s into shape k : s
         | Proj (Term n) Int          -- t.i, i a literal position: peel the first length
         | Cycle (Vec k hint) (Vec k (Term (k + n)))  -- k mutually recursive bodies
Alt n  ::= Alt con (Vec k hint) (Term (k + n))   -- binds the constructor's k fields
con    ::= UserCon hash i             -- constructor i of the declared type with that definition hash
Kind   ::= Bound | Stat
Label  ::= Owner path | Tag label | Axes path | SpaceLabel path | FrameLabel path moving
```

A `Ref`'s hint is the name the author wrote. Hashing ignores it, and the
storage encoding keeps it (§6.1, §7.4), so `:view` shows the author's names and
a unit is decided by the name used (§3.2.12). A `Sample` node's
label is its owner stamp or its `#tag` (§3.2.4). The desugarer writes only
`Owner` and `Tag` on terms. `Axes`, `SpaceLabel` and `FrameLabel` stamp the
types that chart and space declarations mint (§3.9, §3.10, F9).

There are no built-in constructors. `true`, tuples and lists are constructors
of the three declarations that the compiler holds (§2.3), referenced by hash
like any other. With `False`, `True`, `Pair`, `Nil` and `Cons` standing for
those references:

- `if c then a else b` is `Case c [Alt False [] b, Alt True [] a]`.
- `true` is `Con True []`.
- `(a, b)` is `Con Pair [a, b]`, and `(a, b, c)` uses the constructor of the
  three-component tuple type.
- `{a, b}` is `Con Cons [a, Con Cons [b, Con Nil []]]`.

Alternatives follow the constructors' declaration order (`False, True`, then
`Nil, Cons`, and a declared type's as written) and cover every constructor of the
scrutinee's type. The desugarer expands a surface `_` into the missing
alternatives, so Core has no default case. A constructor is referenced by its
type's definition hash and its position, never by name. So renaming a
constructor changes no term (§7.2), and a term's hash depends on the type's
definition, not on what the type is called.

Rules:

- Rationals are stored in lowest terms with a positive denominator.
- **Primitives are saturated**, as PrimOps are in GHC Core. `PrimApp p args`
  always carries exactly `primArity p` arguments, so `a + b` is `PrimApp
  "add" [a, b]`. The desugarer eta-expands a primitive used with fewer
  arguments: `(+ 1)` is `Lam "x" (PrimApp "add" [Var 0, 1])`, and a bare
  `sqrt` passed to `vmap` is `Lam "x" (PrimApp "sqrt" [Var 0])`. The arity
  table is static metadata. Nothing at run time counts arguments.
  Overloading is unresolved here: `PrimApp "eq"` is the overloaded equality,
  and §5.3 records the type it is used at.
- `App` therefore only applies a user function (a lambda, a `Ref` or a
  variable), never a primitive.
- The quantity rule and the `let f x = …` sugar are gone. `3 m` is `PrimApp
  "scale" [Lit 3, PrimApp "m" []]`, `3 km` is the same over `Ref #km`, and `20
  degC` is `PrimApp "pointOn" [Ref #degC, Lit 20]`. Where the spelling does
  not decide, inference does, and the reading is written into the term before
  it is hashed (§3.10, U4, U6). `let f x = e` is `Lam "x" e`.
- A bracket literal whose elements are all constants is one `Lit`. `Pack`
  holds the others, so the two never describe the same value. A negated
  constant is the negative constant itself.
- Free names are resolved to `Ref`s that point at the hash the name has *at
  the time of definition* (§7).
- Within a `Cycle`, member `j` is referenced from inside body `i` as a
  variable bound by the `Cycle` node, so cycle members never contain their
  own hash.

Core is small on purpose. Every later phase (inference, elaboration, hashing,
evaluation) is written against these fifteen constructors, and surface
features are added by extending the desugarer, not the phases.

**Implemented in:** `Metron.Core` (`Term`, `Alt`, `ConRef`, `Label`, `alphaEq`, `traverseChildren`, `refs`, `directUses`, `rewriteRefs`), `Metron.Primitive` (`primArity`), `Metron.Desugar` (`desugarClosed`, `desugarDefinition`, `eta`, `foldConstant`), `Metron.Builtin` (`boolDef`, `pairDef`, `listDef`, `tupleDef`).
**Tested by:** "core"; "traversal"; "desugar"; "data"; "properties" › "typed programs".

### 5.2 The nominal form

The *nominal form* of a Core term is its canonical byte encoding (§6.1):
hints dropped, variables as de Bruijn indices, rationals normalised. Two terms
have the same nominal form exactly when they are alpha-equivalent after name
resolution. The content hash is the SHA-256 of the nominal form.

The hash is **syntactic modulo alpha-equivalence and name resolution**. There
is no beta or eta normalisation and no constant folding: `2 + 3` and `5` are
different terms with different hashes. This keeps hashes stable under
compiler improvements and keeps `:view` output recognisable as what the
author wrote.

Types and elaboration are **not** part of the hash. They are derived from the
term (§5.3) and kept beside it. So adding a type feature never changes the
identity of an existing definition.

**Implemented in:** `Metron.Hash` (`encodeTerm`, `hashTerm`), `Metron.Core` (`alphaEq`).
**Tested by:** "hash"; "properties" › "typed programs"; "codebase".

### 5.3 Typed Core

Typed Core is Core after inference (§4) and *elaboration*. It is explicitly
typed in the manner of System F and GHC's Core, and the evaluator runs it.
Inference and elaboration are one pass. Every elaborated term is checked by
`lint`, a plain type checker in the role of GHC's Core Lint, before it is
stored or evaluated. GHC's Core is System FC, System F extended with
type-equality coercions for GADTs and type families. Typed Core needs no
coercions: it is System F with kinded index arguments.

```
TTerm n ::= TVr (Fin n)
          | TRef hash [idx] hint
          | TPrimApp name type [TTerm n]          -- a saturated primitive at the type it is used at
          | TLit lit [axis]                       -- a constant, at the axes its use gave it (3.9)
          | TLam hint type (TTerm (S n))          -- annotated binder; carries the set of free variables (8)
          | TApp (TTerm n) (TTerm n)
          | TLet hint scheme (TTerm n) (TTerm (S n))
          | TCon con type [TTerm n]               -- at its result type (Nil alone fixes no element type)
          | TCase (TTerm n) type [TAlt n]         -- at its result type
          | TPow (TTerm n) Integer
          | TSample Label (TTerm n)
          | TPack axis type [TTerm n]             -- the element type, kept with no elements; the axes of the new position
          | TProj (TTerm n) Int
          | TTyLam var kind (TTerm n)             -- abstraction over a type, length, shape, dimension, axis, frame or space
          | TTyApp (TTerm n) arg                  -- application to one, by its kind
          | TCycle [(var, kind)] (Vec k (hint, type)) (Vec k (TTerm (k + n)))
TAlt n  ::= TAlt con (Vec k (hint, type)) (TTerm (k + n))
```

These are the fifteen constructors of Core with types added, plus the two
kinded type forms (core.md §5). One pair of type forms serves every kind, so
adding a kind adds no constructor. `TLam` is a pattern over `TLamWith`, which
also holds the set of variables free in the body, computed once and shared, so
that a closure keeps only the variables it uses (§8).

Elaboration does three things:

- **Explicit polymorphism.** Each generalised variable of a scheme becomes a
  `TTyLam` of its kind. Each use of a polymorphic definition becomes the
  matching `TTyApp`s. The evaluator erases them, except where a value's shape
  or dimension comes from them alone (§8): the element type of an empty
  `TPack`, and the instantiated type of `vmap`, `vzipWith` and `timap`.
- **Instance recording.** A `TPrimApp` carries the type it is used at, an
  instance of its scheme. For the relational and overloaded primitives
  (`outer`, `dot`, `eq`, `ne`, the comparisons), that type is the solved
  instance, which lint checks against the constraint.
- **Annotation.** Every binder carries its type or scheme, so each phase
  after elaboration is type-directed without re-inference. Defaulting (§4.2)
  happens at generalisation, so Typed Core has no unresolved constraints.

**Open.** Dictionary passing is not built: an unresolved constraint is
defaulted, never made a parameter (§4.2, §10).

`:core name` prints a definition with every annotation, without `forall`:

```
> let sq x = x * x
> :core sq
sq = Λd5. \(x : Num d5) -> outer x x
> let two = sq 3
> :core two
two = sq @1 3.0
```

`:lint name` re-runs lint on a stored definition and prints its types.

Typed Core is derived data. The codebase keeps it in memory under the Core
hash (`Codebase.derived`, with the schemes) and never writes it to disk. The
store recomputes it on load by inferring and linting each term, dependencies
first (§7.4). The evaluator needs no run-time type information beyond value
tags for printing.

**Implemented in:** `Metron.TCore` (`TTerm`, `TAlt`, `lintClosed`, `lintConstrained`, `freeIndices`, `renderTTerm`), `Metron.Infer` (`elaborateClosed`, `abstractOver`, `instantiate`, `zonk`), `Metron.Check` (`checkCore`), `Metron.Codebase` (`Codebase`, `lookupTyped`).
**Tested by:** "typed core"; "lint regressions"; "soundness"; "properties" › "typed programs"; "properties" › "blind programs".

---

## 6. Hashing

### 6.1 Canonical encoding

A term is encoded to bytes with `bytestring`'s `Builder`, one tag byte per
constructor, every variable-length field prefixed by its length. The hash is
the SHA-256 of the encoding, displayed as a base32hex prefix: `#a3f9k`.

| Tag | Node | Payload |
|---|---|---|
| 0x00 | `Var i` | varint `i` |
| 0x01 | `Ref h idx` | 32 bytes `h`, varint `idx + 1` (0 means no index) |
| 0x02 | `PrimApp name args` | the name as text, then each argument (the arity table fixes the count) |
| 0x03 | `Lit tensor` | varint rank, each length as a varint, then each value as sint numerator and varint denominator, row-major |
| 0x05 | `Lam t` | `t` |
| 0x06 | `App f a` | `f`, `a` |
| 0x07 | `Let e b` | `e`, `b` |
| 0x09 | `Pow t n` | `t`, sint `n` |
| 0x14 | `Sample l distribution` | label, distribution term |
| 0x0C | `Pack ts` | varint count, each `t` |
| 0x0E | `Cycle ts` | varint count, each `t` |
| 0x0F | `Proj t i` | `t`, varint `i` |
| 0x10 | cycle-variable placeholder | no payload, only in the ordering hash of §6.2, never in a stored term |
| 0x11 | `Con con args` | constructor reference, varint count, each argument |
| 0x12 | `Case s alts` | `s`, varint count, each alternative: constructor reference, varint `k`, (`k` hints in the storage encoding), the body at depth `+ k` |

No other tag is written, and the decoder refuses any other ("unknown term
tag"). The decoder also refuses an unknown primitive name, a variable index
that escapes its scope, and a placeholder.

Text is a varint byte length and the UTF-8 bytes. A label is one byte and its
text: 0 owner, 1 tag, 2 axes, 3 space, and 4 frame, which adds one byte, 1
for a moving chart and 0 otherwise. The desugarer writes only owner and tag
labels on a term, but every kind decodes there. In the *storage* encoding
(§7.4), every `Ref` is followed by the name the author wrote, and every binder
by its name hint: a `Lam` or `Let` hint after its tag, a `Cycle`'s hints after
its count, and an alternative's hints after its `k`. The canonical encoding,
and so the hash, has neither. The owner stamp is the full path of the
enclosing definition (§3.2.4), so the hash of a definition that declares
uncertainty depends on its name and its namespace. Nothing else in a term's
hash does.

A constructor reference is the 32-byte definition hash of its type and the
varint position of the constructor in it.

**Declared types.** A declared type (§2.3) is hashed separately, from its own
canonical encoding: the varint parameter count and one kind byte per
parameter, the varint constructor count, and for each constructor a varint
field count and each field type, then the label.

| Kind byte | Kind |
|---|---|
| 0 | type |
| 1 | length |
| 2 | shape |
| 3 | dimension |
| 4 | axis |
| 5 | frame |
| 6 | space |

The label is one of: 0 and the type's full path (an owner stamp), 1 and an
empty text for `structural`, 2 and a chart's or a vector space's full path for
the axis type its declaration mints (§3.9: no parameters, one constructor with
no fields), 3 and a space's full path for the type a `space` declaration mints,
or 4, a chart's full path and a byte, 1 for a moving chart, for its frame type
(§3.10, part F). No source `data` declaration produces labels 2 to 4, so a
user's `data Eci = Eci` never equals a minted type. Types use tags of their
own:

| Tag | Type | Payload |
|---|---|---|
| 0x21 | `Tensor σ δ` | shape, dimension |
| 0x26 | `a -> b` | `a`, `b` |
| 0x27 | variable | varint id (a parameter: 0 .. k-1) |
| 0x28 | `T a…` | 32-byte hash, varint count, each argument as a kind byte and its value |
| 0x2A | `Unit δ` | dimension (internal, §3.10, U1) |
| 0x2B | `Point φ` | frame (§3.10, F4) |
| 0x2C | `Chart φ` | frame (§3.10, F4) |
| 0x2D | `Diff φ`, `Coords φ` | frame, then 0 for `Diff`, or 1 and a dimension for `Coords` (dimension 1): the residual amount type until the space's shape is known (§3.10, F4) |

The parts:

- A **shape** starts with a byte. 0 is `[]`. 1 is a position with anonymous
  axes, followed by a length and a shape. 2 is a shape variable, followed by
  its id. 3 is a position whose name slot is not anonymous (§3.9), followed
  by a length, an axis and a shape. So the anonymous set of size `k` encodes
  byte for byte as a bare length `k`.
- An **axis** is 0 for anonymous, 1 and the 32-byte hash of a named set, or 2
  and a variable id.
- A **length** is 0 and a varint literal, or 1, a variable id and a varint
  offset, or 2, a shape variable id and a varint offset for `rank s + k`
  (§4.1).
- A **dimension** is a varint atom count and, for each atom, 0 and a
  base-dimension byte or 1 and a variable id, then the sint exponent.
- A **frame** (§3.10, F9) is its slot (0 and the 32-byte hash of its minted
  frame type, or 1 and a variable id), then its axis and its space. A
  **space** is its slot (0 and the hash of its minted space type, or 1 and a
  variable id), then its shape, dimension and base axis.
- A declared type's **argument** is its kind byte and then a type, length,
  shape, dimension, axis, frame slot or space slot, by the kind.

A recursive occurrence of the type being declared is `0x28` with the
all-zero hash, so the definition never contains its own hash. A length
parameter has a companion axis parameter after the written ones (§3.9).
`Bool`, tuples and lists are `0x28` on the hashes of their declarations
(§2.3), which this encoding therefore fixes: `structural data Bool = False |
True` is no parameters, two constructors of no fields, and the structural
label.

`varint` is unsigned LEB128. `sint` is one sign byte followed by a varint byte
length and the big-endian magnitude bytes, so arbitrarily large integers
encode canonically. A long integer is written by halves, so its encoding costs
`n log n`. The encoding is also the on-disk format (§7.4) and must
round-trip.

The hash depends on the desugaring rules and this encoding as well as on what
the user wrote, so a change to either re-identifies stored definitions.
core.md, "What the hash depends on", records the consequences and the policy
for stores.

**Implemented in:** `Metron.Hash` (`encodeTerm`, `encodeStored`, `decodeStored`, `hashTerm`, `decodeTypeDef`, `hashHex`), `Metron.Encode` (`encodeTypeDef`, `hashTypeDef`, `encType`, `varint`, `sint`, `text`).
**Tested by:** "hash"; "store"; "axis slots"; "named axes"; "internal units and public amount arithmetic"; "properties" › "typed programs"; "fixed-point series agree with the exact-rational ones within both bounds" › "a long integer encodes as it did, byte for byte".

### 6.2 Hashing cycles

Mutually recursive definitions form a cycle. Hashing follows Unison's
`hashCycle`:

1. Take one strongly connected component of the binding group.
2. Replace every reference from one member to another by a *cycle variable*.
3. Hash each body with all cycle variables replaced by one placeholder (tag
   0x10). Sort the members by that hash. This fixes an order that depends
   only on content.
4. Assign de Bruijn indices in that order and hash the whole `Cycle` term.
   Call it `H`. Member `i` is referenced from outside as `Ref H i`.

Two members whose bodies are identical up to cycle variables tie in step 3.
Any order between them produces the same `Cycle` term, so the hash is
unaffected. A self-recursive definition is a one-member cycle. A component of
one member that does not reference itself is a plain term, not a cycle, and
gets `Ref H` with no index.

Walkthrough:

```
let even n = if n == 0 then true  else odd  (n - 1)
let odd  n = if n == 0 then false else even (n - 1)
```

Both names are free in each other's bodies, so they form one component. After
step 2, each body is a `Lam` whose `Case` has a constructor `true` or `false`
in one alternative and an `App` of the cycle variable in the other. In step 3
the two placeholder hashes differ, because the constructors differ. Suppose
`odd` sorts first. The order is `[odd, even]`: `odd` is member 0 and `even`
is member 1. To enter the two `let`s in the other order produces the same
component, the same sort, the same `Cycle` term and the same `H`. The
namespace maps `odd ↦ Ref H 0` and `even ↦ Ref H 1`.

**Implemented in:** `Metron.Resolve` (`enterCycle`, `enterComponent`), `Metron.Hash` (`placeholderHash`, `hashTerm`).
**Tested by:** "hash"; "codebase"; "evaluation" › "mutual recursion through a cycle: even and odd".

### 6.3 Dependency analysis

The free names of each statement in a binding group are collected. Names that
the codebase already has resolve to `Ref`s at once and are not edges. The
remaining edges feed `Data.Graph.stronglyConnComp`. Components are processed
in topological order: resolve, hash, infer types, store. A statement that
names something that is neither in the group nor in the codebase is an error
for the whole group, and nothing from the group is stored.

**Implemented in:** `Metron.Resolve` (`processGroup`, `enterGroup`, `freeNames`, `enterComponent`).
**Tested by:** "codebase"; "end to end".

## 7. Codebase and names

### 7.1 Model

The codebase holds terms by hash and labels that point at them. Its record
is `Metron.Codebase.Codebase`:

```
Codebase = { terms       :: Map Hash Term                 -- Core, the hashed content
           , derived     :: Map Hash ([Scheme], TTerm)     -- inferred types, Typed Core; recomputable
           , names       :: Map Name Reference             -- current label → reference
           , history     :: Map Name [Reference]           -- newest first
           , units       :: Set Name                       -- names declared with `unit` (3.2.12)
           , charts      :: Set Name                       -- names declared with `chart` (3.6)
           , preferences :: Set Text                       -- display preferences as written (3.2.12)
           , typeDefs    :: Map Hash TypeDef               -- declared types by definition hash (2.3)
           , typeNames   :: Map Name Hash                  -- type labels
           , conNames    :: Map Name (Hash, Int)           -- constructor labels: a type and a position
           , fieldNames  :: Map Name (Hash, Int, Int)      -- record field labels: type, constructor, position
           , uses        :: [Use]                          -- the stored uses, oldest first (7.7)
           , signatures  :: Map Name Scheme                -- signatures by name (4.8)
           }
Reference = Reference Hash (Maybe Int)                     -- a hash and an optional cycle index
```

`derived` holds one scheme per member, so a cycle has several.

Entering a definition `x = e` (by `:add` or `:update`, §7.5) does these
steps in order:

1. It resolves the free names in `e` to their *current* references.
2. It hashes the result (§6).
3. It infers the type scheme.
4. It stores `(term, scheme)` under the hash. If the hash is present, this
   step does nothing.
5. It points `x` at the reference and prepends the reference to `history
   x`, unless `x` already points there.

Entering an identical body again changes nothing. A body that differs only
in a bound variable's name also changes nothing, because Core has no
names.

**Implemented in:** `Metron.Codebase` (`addTerm`, `bindName`, `historyOf`, `lookupName`), `Metron.Resolve` (`processGroup`, `storeTerm`).
**Tested by:** "codebase".

### 7.2 Versioning is relabelling

Rebinding a name never changes an earlier definition that mentions it,
because that definition holds the hash, not the name. A dependent moves to
a new version only by propagation (§7.5). Propagation is automatic on
`:update` and explicit with `:upgrade`. This trace holds propagation back
to show the stale state:

```
> let x = 5
> let y = x + 1
> :add                   -- terms: #k1 = Lit 5, #k2 = add (Ref #k1) (Lit 1);  x ↦ #k1, y ↦ #k2
> let x = 6
> :update --no-upgrade   -- #k3 = Lit 6;  x ↦ #k3;  history x = [#k3, #k1];  y untouched
> y
6                        -- y's term still refers to #k1, which is 5
> :view y
y = x#k1 + 1             -- x no longer points at #k1, so the reference shows as stale
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

A plain `:update` does the `:upgrade` step at once and prints the same
report.

**Historical references.** `:view` prints a `Ref` in one of three forms:

- by its current name, when the name still points at that hash
- as `name#hash`, when the name has moved on
- as `#hash`, when nothing names it

Both hash forms can be written in expressions (§2.1). A named reference
searches the name's current binding and its history through the usual
namespace lookup, also after the name is removed. A bare reference searches
all stored terms. A missing or ambiguous prefix is an error, and an
ambiguity report shows the full hashes. A named reference cannot select a
version that was never associated with that name. A hash reference
bypasses local binders and new definitions in the same binding group. The
stored type of the selected term decides whether it is a unit or a chart,
not the flags of the current name. A declared type's constructors are not
term hashes, so this syntax cannot reach them.

A bare hash used as an argument takes parentheses: `f (#hash)`. To project
from a historical tensor, write `(v#hash).0`, because `#hash.0` selects a
cycle member. A glued `name#hash` is a reference, and a separated `#label`
is the uncertainty postfix (§3.2.4).

A hash reference selects a Core reference. It is not a permanent pin:
stored dependents still follow the upgrade rules. Propagation does not
rewrite an accepted replacement itself. So replacing `x = 5` with `x =
x#old + 1` gives `6`, not `7`. Other dependents still upgrade, also a
dependent that shares the replacement's hash. A reference to a
definition's own past is intentional, and `:todo` does not list it as
stale.

A reference into a cycle prints as `#hash.i`. `:view` of a cycle member
shows that member's body, with the other members by their current names.

Within one input, a second definition of the same name is an error, not a
rebinding. Rebinding happens between inputs. The standard library (§7.7)
is names like any other. For example, rebinding `astro.G` to a newer CODATA
value with `:update --no-upgrade` leaves every existing function on the old
`G#…`. `:dependents astro.G` lists them, and `:upgrade astro.G` moves them.

**Re-stamping.** Relabelling never changes a hash, with one exception. Two
kinds of label are stamped with their full path: a definition whose term
carries an owner stamp (a `sample` written in it,
§3.2.4), and a nominal type (§2.3). `:rename` and `:move` of such a label,
alone or as part of a namespace, re-stamp it with the new path and hash it
again. It then has the hash that its text gets when it is entered under
the new name. Everything that mentions it follows, dependencies first, as
`:update` propagates:

- a type whose fields use a re-hashed type
- a definition that uses a re-hashed type's constructors
- every dependent of a re-hashed definition, checked again and bound again

A cycle's other members, and a type's constructor and field labels, move
with it. The change is all or nothing: if anything fails to check,
nothing changes. The report says what moved:

- `re-hashed data mechanics.Body` for a type
- `re-hashed lab.x #k1 -> #k5` for each moved definition whose hash changed
- `upgraded b #k2 -> #k6` for each dependent outside the move

History keeps the old path on the old hash. A cycle re-stamped in place
keeps its members' order. Entering its text again can give another order,
and so another hash for the same cycle.

**Signatures are labels.** Signatures (§4.8) are kept per name, as the
`unit` and `chart` flags are. `:rename` and `:move` move a signature with
its name, and follow a re-hashed type that the signature mentions.
`:unname` removes it. `:alias` does not copy it: an alias names the hash,
and a hash has no signature, so `f` can be signed while its alias `g` is
not. Rebinding a signed name to a new version keeps the signature only if
the signature holds of the new definition (§4.8).

**Implemented in:** `Metron.Codebase` (`bindName`, `historyOf`, `findByPrefix`, `showReference`, `dependents`), `Metron.Update` (`propagateNamed`, `propagateScoped`, `restamp`, `staleReferences`), `Metron.Session.Names` (`relabel`, `removeLabel`), `Metron.Source` (`viewReference`).
**Tested by:** "codebase" › ":update --no-upgrade leaves dependents on the old version", ":upgrade moves stale dependents to the current version", "hash references validate missing, malformed and ambiguous prefixes", "historical names respect namespace lookup and explicit absolute paths"; "namespaces".

### 7.3 REPL commands

`:help` prints this list, and an unknown command is refused with it.
`Metron.Command.commandDescriptions` is its one source, shared with
completion.

```
Scratch and codebase (7.5)
:add                    store pending definitions whose names are new; a conflict refers to :update
:update [--no-upgrade]  store pending definitions, binding existing names again, then propagate
:upgrade name           move dependents still on old versions of name to its current version
:todo                   pending definitions and stale references
:scratch                list pending definitions, a signature as `pending: area :: Shape -> Num (m^2)`
:forget name            drop a pending definition and its pending signature
:edit [name|namespace]  open the codebase but the library, a namespace (a library one included), or one
                        definition or type in $VISUAL or $EDITOR as source, and reconcile the saved file
                        with the codebase: add, update (with propagation), remove; all or nothing (below).
                        Without an editor, print the source instead: for one name, the definition or
                        data declaration ready to paste back, in a namespace block when it is outside
                        the current namespace (7.6)
:edit --file path [name|namespace]
                        reconcile a file without opening an editor (one kept after an error)

Inspection
:ls [glob|namespace] [--all|--units|--charts|--types] [: type]
                   names with their types, sorted. Alone: the current namespace's own labels, then one
                   line per namespace directly under it, `namespace si (799 names)`. A word that names
                   a namespace lists everything under it, relative to it, data lines included. --all
                   lists everything by full path. A glob (* anywhere, else a substring; on the full
                   path or its last segment), a kind, or a type query searches everything. A type
                   query's unknown lowercase names are variables (no forall needed: a query is a
                   pattern), matched by unification both ways. A signed name shows, and matches, its
                   signature (4.8). Types print headed by forall. --types lists a chart's minted frame
                   as `frame lvlh` and a space as `space GCRS = Vec 3 m`; minted axes go by their
                   chart's name (3.9, 3.10). A unit shows, and matches, the type of one of it,
                   `unit kPa : Num (kg/(m*s^2))`, so every type shown reads back (3.10, U9)
:type expr         the inferred type scheme, headed by forall when it has variables (forall a. a -> a);
                   a signed name's signature, as its uses see it (4.8); the type of `it`, so a value
                   that is not a function has anonymous axes where nothing fixes them (3.9)
:hash name         the current reference of name
:names #hash       every name that points at the hash, current or historical
:history name      the references the name has pointed at, newest first
:view name         the term, with references printed as in 7.2; for a type, its declaration; a chart
                   with its keyword, `chart degC on ITS90 at 273.15 K`; a space as `space ITS90 = Num K`
                   (3.6, 3.10). A name the uses offer as several shows each after a `-- full.path`
                   line, types first and then by path (`:view TT` shows `time.TT`, a space, and
                   `si.TT`, the teratesla)
:core name         the Typed Core (5.3) with every annotation
:lint name         run lint again on a stored definition and print its type(s)
:dependents name   definitions whose terms reference the current reference of name
                   (:hash, :history, :core, :lint and :dependents take the one definition among
                   several a name offers, and list them when there are several:
                   "`h` is both `physics.h` and `time.h`; write one of them")
:alias new old     point new at old's current reference; for a namespace, give every label under old
                   the same label under new
:unname name       remove the label (of a definition, a type or a constructor; .f for a field); the
                   term stays; for a namespace, every label under it, with the count
:rename old new    relabel a definition, type, constructor or field, or every label under a namespace
                   (7.6); history keeps both names; all or nothing
:move name… ns     :rename each name (a label or a namespace) to ns.<its last segment>

Namespaces (7.6, 7.7)
:namespace [path|.] show or set the current namespace (a full path); . is the root
:uses              the uses in effect: the stored ones, marked (stored), then the session's
:use path [as a]   add a stored use, kept in the codebase (7.7)
:unuse path        drop a use, by its path or its alias: a stored one when one matches (and say so),
                   else the session's
:stdlib upgrade    take the shipped standard library's newer definitions (7.7)

Session
 :set              list the controls
:set arithmetic rational|double
:set propagation montecarlo
:set precision n   rational approximation and display precision
:set unicode on|off
:set samples n | seed n | cores k
:set roundingAnalysis off|stochastic
:set roundingSamples r

:set memory|steps|depth|digits|components|outcomes:set memory|steps|depth|digits|components|outcomes n | time s|off
                   the resource limits (8.1)
:prefer [unit]     print values of the unit's dimension in it (3.2.12); alone, list the preferences
:unprefer unit     remove that preference
:load file         enter a file into the scratch as one binding group; its `use`s last for the file
:export [namespace] [file]
                   the stored codebase but the library, or one namespace (a library one included),
                   as source that :load reads back (7.4); to the file when one is given. A word
                   that is no namespace is the file if it has a / or a ., else it is refused as a
                   misspelling
:store             the directory of the store in use, or "no codebase: running in memory"
:colour [on|off]   colour the REPL's output; alone, say whether it is on (a REPL setting, below)
:help              this list
:quit              also :q
```

`:set` lists precision, unicode, samples, seed, arithmetic, propagation,
roundingAnalysis, roundingSamples and cores, followed by resource limits.
Defaults are specified in §8.2.1. Library sessions use one core.
The executable uses the machine's logical core count.
`metron --set NAME VALUE` changes a control at startup.
Completion and printed controls share `Driver.settingValues`.

**Editing in place.** `:edit` is a round trip through a text editor. It
has three forms, and they work alike:

- `:edit` alone takes the stored codebase except the library's namespaces,
  which is what `:export` writes.
- `:edit orbital` takes a namespace. `:edit si` takes the SI part of the
  library.
- `:edit period` takes one definition or `data` type, with the other
  members of its cycle when it has one, because a member alone enters
  again as another term.

The steps:

1. **Export.** The REPL writes the scope to a new temporary file,
   `metron-edit-….metron`, in the system's temporary directory, in the
   `:export` format (§7.4): the stored `use`s as `use` lines, then
   `namespace` blocks by full path from the root. A header comment says
   what saving does. The file is read from the root with no `use` of the
   session, as it was written, so the current `:namespace` and the
   session's `use`s do not change what it means.
2. **Edit.** The REPL runs `$VISUAL`, else `$EDITOR`, through `sh -c` (so
   `EDITOR="emacs -nw"` works), gives it the terminal, and waits.
   haskeline holds the terminal only while it reads a line, so the prompt
   is sane afterwards. A non-zero exit, or a file saved unchanged, changes
   nothing. The REPL says `nothing to do: the file was not changed` and
   deletes the file.
3. **Reconcile.** The saved file is entered as one binding group on top of
   the codebase, as the scratch is (§7.5). It is compared with the
   codebase by full path, over every kind of label: definitions with their
   `unit` and `chart` flags, types, constructors and fields.
   - *Added*: the file defines the label, and the codebase did not have it.
   - *Updated*: the file binds the label to another reference. When the
     old term, with the group's new references and a replaced type's
     constructors put in, is the new term, only what it uses moved, and
     the report says *upgraded* instead.
   - *Removed*: a label of the scope that the file does not define. It is
     removed as `:unname` removes it, and history keeps the term. Nothing
     is removed when the scope is one name. A definition moved to another
     `namespace` block is a removal and an addition, because a label is
     its full path.
   - *Unchanged*: everything else. The same text under the same path gives
     the same hash. This holds also for a `sample` definition and a nominal
     type, since their owner stamp is the full path (§3.2.4).

   A definition outside the scope that the file defines is added or
   updated in the same way. Then propagation moves the dependents outside
   the file to the new versions, as `:update` does. It also moves the
   definitions that build or match a replaced type's constructors, matched
   by name. A dependent that no longer checks is left on its version with
   the reason. A dependent of a removed definition keeps its reference and
   is reported stale. A type outside the file whose fields use a replaced
   type keeps the old one, and the report says so.
4. **All or nothing.** Each of these refuses the edit and changes nothing:
   - a parse, type or namespace error, shown with its excerpt at the line
     in the file
   - an expression in the file
   - a file that no longer defines the one name it was opened for
     (``the file no longer defines `area`; use :unname to remove it``)
   - a file that removes every label of the scope, such as an emptied
     buffer (``the file defines nothing in `orbital`; if you mean to
     remove it all, use :unname orbital``)
   - a definition named `it`
   - a pending scratch that no longer checks on top of the result

   After an error the file is kept, and the REPL prints its path and the
   command that resumes from it: `:edit --file
   /tmp/metron-edit-1234-0.metron orbital`.

The report reads as `:update`'s: `added data T` or `updated data T`,
`added x`, `updated x #old -> #new`, `removed x` (and `removed data T`,
`removed constructor C`, `removed field f` for what an edited type left
behind), `upgraded y #old -> #new`, `left y on #r: why`, `left data P on
the old version of T`, `left y stale: it uses x#r, which was removed`,
`signed f` and `unsigned f` for a signature line (§4.8) added, changed or
deleted on a definition the file keeps, or `nothing changed`. A signed
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
(`metron -i`, one-shot mode, or neither `VISUAL` nor `EDITOR` set),
`:edit` prints the source it opens otherwise and a note that says why.
For one name, it prints the statement, spelled for the current namespace
and ready to paste back (a pending definition too). For a namespace or the
codebase, it prints the export. In one-shot mode the note goes to stderr,
so the source stays pasteable.

**Unicode output.** With `:set unicode on`, printed values, `:type`,
`:view`, `:edit` and the `:prefer`
message use these spellings from the table in §2.8. Nothing else changes,
except the echo below.

| ASCII | Unicode | Where |
|---|---|---|
| `^2` `^-1` | `²` `⁻¹` | unit exponents (`9.81 m s⁻²`, `5 km h⁻¹`), dimensions in types (`Num (m/s²)`), powers in `:view` (`x²`) |
| `->` | `→` | function types, lambdas and case alternatives |
| `\` | `λ` | lambdas: `λx → x² + 1` |
| `<=` `>=` `/=` `\|\|` | `≤` `≥` `≠` `∨` | operators in `:view` |

`*` stays `*`, because `×` is the cross product. `/`, `&&`, `sqrt`,
`forall` and names such as `pi` and `deg` keep their ASCII spelling. `∀`
reads as `forall` but is not printed. `√` is not printed for `sqrt`,
because `√` is a prefix operator and `sqrt` an application, which bind
differently. `π` and `°` are names, not syntax. `·`, `∧`, `⊙` and `⊘` print in unicode in both modes. A power whose base does not end
in an atom keeps its caret, since a superscript must be glued to an atom.
Every unicode form lexes to the same tokens as its ASCII form, a
superscript standing for its caret, so output reads back either way.
Error messages, `:core` and `:lint` stay in ASCII.

**The echo.** With `:set unicode on`, statement lines with an alternative
unicode spelling are echoed before evaluation. For example, `2^3` echoes
as `2³`. The echo preserves spacing and comments outside replaced tokens.
Commands, files and lines with no alternative spelling are not echoed.
The echo lexes to the same tokens as the input.

**The last result.** After an expression statement evaluates, `it` names
that expression for later expressions and for the inspection commands.
`1 + 2` then `it * 2` prints `6`, `:type it` gives its type, `:view it`
prints `it = 1 + 2`, and `:core`,
`:hash` and `:lint` take it as they take a definition. On a line with
several expressions, each one is `it` for the next. `it` is the
expression, not its printed value. It is hashed as a definition is, so a
`sample` in it preserves the same latent input every time it is used. An input that fails leaves the previous `it`. Before the
first expression, `it` is an unknown name. `it` is local to the session
(§7.5): `:ls`, `:edit`, `:alias` and `:dependents` do not see it.

#### The REPL

The interactive REPL adds editing aids on top of the commands. None of
them changes what an input means or the text it prints.

**Completion.** TAB completes the word before the cursor:

- at the start of a line, a `:` command
- after `:set`, the setting, and after `:set unicode` and `:colour`, `on`
  or `off`
- after `:load` and `:edit --file`, a file name
- after a `.` glued to a value, a record field name (`b.ma` gives
  `b.mass`)
- elsewhere, a name the session sees (definitions, units, types and
  constructors, pending ones included) or a keyword

The standard library has many hundreds of names, so a short prefix can
list many candidates.

**Unicode by name.** A backslash, a name, then TAB enters a character, as
in Julia: `\mu` gives `μ`. When the typed name is a whole entry, the REPL
replaces it, so `\prime` gives `′`. Otherwise TAB
lists the entries that start with it. The table is in `Metron.Unicode`:

| Names | Result |
|---|---|
| `\alpha` … `\omega` (`\lambda` is the lambda `λ`, `\pi` is `π`) | Greek letters |
| `\Gamma` `\Delta` `\Theta` `\Lambda` `\Xi` `\Pi` `\Sigma` `\Upsilon` `\Phi` `\Psi` `\Omega` | the capitals that do not look like Latin ones |
| `\micro` `\ohm` | `μ` `Ω`, the forms the lexer folds `µ` and `Ω` to |
| `\to` `\otimes` `\cdot` `\times` `\odot` `\oslash` `\div` | `→` `⊗` `·` `×` `⊙` `⊘` `÷` |
| `\le` `\ge` `\ne` `\or` `\neg` `\wedge` `\star` `\circ` `\sqrt` | `≤` `≥` `≠` `∨` `¬` `∧` `⋆` `∘` `√` |
| `\deg` `\degC` `\degF` `\prime` `\dprime` | `°` `°C` `°F` `′` `″` |
| `\^0` … `\^9` `\^-` | `⁰` … `⁹` `⁻` |
| `\_0` … `\_9` | `₀` … `₉`, inside identifiers |

`\leq`, `\geq`, `\neq`, `\vee`, `\lnot`, `\rightarrow` and `\pprime` are
aliases. There is no `\and`: `∧` is the wedge product, and boolean and is
`&&` only (§2.8). Every entry lexes to the same tokens as its ASCII
spelling in §2.8, or is a letter that is valid in an identifier. Two kinds
of entry have tokens of their own, a superscript and `√`. For these, the
value must equal that of the caret power or of `sqrt`. The test suite
checks all of this against the lexer.

A word that starts with `\` completes from this table only, never from
names. Nobody presses TAB in a lambda such as `\x -> x`, so the two uses
never meet. TAB after `\x` offers `\xi`.

**Colour.** The REPL colours its output when stdout is a terminal, `TERM`
is not `dumb` and `NO_COLOR` is not set. The theme uses only the 16 ANSI
colours, so it shows on any terminal. It has no dim text, because some
terminal themes do not show dim text.

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
and the input echo of `metron -i`. An error's carets stay under the
excerpt, because colour codes take no columns. The name in a `name : type`
line stays plain. Its `unit` or `chart` is a keyword.

Details of the rules:

- In a type, a name is cyan only inside `[…]`. So a type variable such as
  `m` or `g` stays plain in `(g → m) → {g}`.
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
an excerpt stays plain. A line also counts as not lexing when NFC changes
its length or when it has a tab, because then the spans do not index the
printed text. Colour only adds escape codes. Remove them and the text is
the same as without colour.

`:colour on` and `:colour off` override the default. This is a setting of
the REPL, not of the session: `:set` does not list it, and the one-shot
and file modes never colour.

**Continuation lines.** An input can span several lines. After each line
the REPL decides whether the input is finished. If it is not, the REPL
reads another line at the prompt `… ` and appends it after a newline. The
input goes on when:

- a `(`, `[` or `{` is not closed
- its last token cannot end an input: `=`, `->`, `\`, `|`, `,`, `;`, a
  backtick, `√`, an infix operator (`+ - * / ^ == /= < <= > >= && || : .
  ∘` and the others of §2.5), or a keyword other than `true`
  and `false` (`of`, `where`, `in`, `then`, `else` and the rest)
- a line ends in `of` or `where`. The entries of that block follow on
  indented lines, and the input goes on until a blank line.

The decision reads the lexer's tokens, so a comment never counts: `x --
(` is finished, and so is `1 + 2 --`. A field access glued to a value
(`b.mass`) is one token and ends an input. A `.` with nothing after it is
composition, so it does not. A `:` command never goes on. Text that does
not lex is fed as it stands, so the lexer's error shows.

A blank line at the continuation prompt ends the input as it stands. The
input is then fed, and an unfinished one gives the parser's error as
usual. Ctrl-C or Ctrl-D at the continuation prompt abandons the input and
prints `(input abandoned)`. At the `> ` prompt they end the session.

A continuation line keeps its indentation, and the layout rule (§2.2)
reads the input as it reads a file. A line indented further than the
first line continues its statement. A line at the first line's column
starts a new statement in the same binding group.

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
open. So a later line that starts with `where` or `else` is not joined to
a finished line before it: `let f x = y * 2` is fed before `  where y = x
+ 1` is read. Put the `where` at the end of the first line, or use
`:load`.

`metron -i` reads continuation lines in the same way, so a piped script
can hold multi-line definitions. Each line is echoed after the prompt it
was read at, `> ` or `… `.

**History.** The line history is the file `history` in the codebase
directory (§7.4). With `--no-codebase` there is no history file. Each
physical line is one entry, so a multi-line input is recalled line by
line. haskeline writes its history file one entry per line, and its line
editor does not redraw an entry that contains a newline, so the lines are
not joined into one entry.

**Implemented in:** `Metron.Command` (`commandDescriptions`, `commandHelp`), `Metron.Driver` (`feed`, `feedFile`, `setSetting`, `settingValues`, `settingNames`), `Metron.Limits` (`limitSettings`), `Metron.Edit` (`editRequest`, `applyEdit`, `editorNote`), `Metron.Repl` (`complete`, `continuation`, `needsMore`, `classify`, `paint`, `highlight`, `echoInput`), `Metron.Unicode` (`completions`, `lookupName`), `Metron.Pretty` (`respell`). The editor, `:store`, `:colour`, `:load` and the history file are in `src/Main.hs`.
**Tested by:** "repl"; ":edit, the editor round trip"; "unicode echo"; "it, the last result"; "codebase" › ":edit prints a definition as source", ":ls lists names with their types, filtered by glob, kind or type query"; "standard library" › ":ls lists a unit with a type that reads back: one of it (design §3.10, U9)"; "independent arithmetic and grouped rounding".

### 7.4 CLI and persistence

```
metron                     REPL when stdin is a terminal; otherwise read a program from stdin, as -f does
metron 'expr'              one-shot: print the value and exit 0; on an error, print it to stderr and exit 1
metron -f file.metron      load a file as a binding group and print its bare expressions
metron -i                  the REPL loop on stdin, line by line, with each line echoed after its prompt
metron --codebase DIR …    use an explicit store
metron --no-codebase …     run in memory, seeded with the library
metron --set NAME VALUE …  start with a setting changed, as :set NAME VALUE (any number of times)
metron --merge OTHER       merge the store at OTHER into this one, leaving OTHER as it is
```

A codebase on disk is a directory:

```
format             "metron codebase 12": the store's format
terms/<hex hash>   one term per file: the canonical encoding of 6.1 with each binder's
                   name hint after its tag and each reference's written name after it, so
                   :view keeps the author's names and units are decided by the name used;
                   the hash is computed again on load
types/<hex hash>   one declared type per file, in the encoding of 6.1; loaded before the
                   terms, which can mention them
names.log          append-only, one event per line:
                     <unix time> bind <name> <hex hash>[.<i>]
                     <unix time> unname <name>
                     <unix time> unit <name>
                     <unix time> chart <name>                    -- a chart flag (3.6)
                     <unix time> unflag <name>                   -- a name lost its unit or chart flag and stays bound
                     <unix time> prefer <unit text>
                     <unix time> unprefer <unit text>
                     <unix time> type <name> <hex hash>          -- a type label
                     <unix time> con <name> <hex hash>.<i>       -- a constructor label
                     <unix time> field <name> <hex hash>.<i>.<j> -- a record field label
                     <unix time> use <path> [as <alias>]         -- a stored use (7.7)
                     <unix time> unuse <path> [as <alias>]
                     <unix time> sig <name> <type>               -- a signature (4.8)
                     <unix time> unsig <name>
history            the REPL's line history
```

A `sig` line holds the signature as text that reads back at the root,
whatever comes after it. The text is ASCII, names declared types by their
absolute paths (`.Shape`, so the stored `use`s cannot change what it
means), and binds its variables by `forall` (§4.8), so a variable shadows
a unit of its name: `sig same forall s d. Tensor s d -> Tensor s d`. On
replay it is parsed and converted as a written signature is (§4.8), a
sized binder sized. It is kept when its name is bound to a definition it
holds of. Otherwise it is skipped with a note. Sig lines come after every
other line of a sync, so the labels they name exist. `unsig` is written
when a name loses its signature, whether or not it stays bound.

Types and Typed Core are not stored. The loader computes them again by
typechecking and linting each term, dependencies first. This is cheap: the
standard library's 800 definitions take about 30 ms. Terms are only ever
added, so two stores never conflict on terms. The log is the one thing
with order, and two stores merge by concatenating their logs and sorting
by time, the last writer winning per name.

**Merging.** `metron [--codebase DIR] --merge OTHER` merges into the store
that `metron` uses otherwise:

- Both stores open as usual, OTHER first. So a store of another format is
  refused (below), and so is a directory that is not a store. Either is
  left untouched.
- Every file in OTHER's `terms/` and `types/` that DIR lacks is copied
  after its hash is checked, as on load. A file that is already there is
  the same content and is never overwritten. A corrupt one is skipped with
  a note.
- OTHER's log lines that DIR does not have are added. The whole log is
  then stably sorted by its leading time and written through a temporary
  file, after the terms, so an interrupted merge never leaves a name
  pointing at a missing term. On equal times DIR's line comes first and
  OTHER's wins. A line with no readable time sorts as if at time 0 and is
  reported.
- Merging again adds nothing. The `history` file is DIR's own and is
  neither copied nor touched.

The summary gives the terms, types and log lines brought across, then the
notes.

**Where the store is.** The user store is `$XDG_DATA_HOME/metron/`, and
the daily calculator uses it. A project-local `.metron/` directory, found
by walking up from the current directory, shadows the user store.
`--codebase DIR` names one explicitly, and `--no-codebase` runs in memory.
`:store` prints the directory in use. iapetus commits its `.metron/` to
git.

**Decided.** Decoding rejects zero rational denominators, invalid integer
signs, and indices or dimensions outside the machine `Int` range before
constructing values. Byte lengths and collection counts must fit the
remaining input. Tensor element counts are computed as integers before
checking their range, so shape multiplication cannot wrap. These are
decoding errors: load and merge report and skip the corrupt object rather
than raising an arithmetic exception. Valid encodings and hashes do not
change.

Decoder regression coverage: "store" › "malformed stored scalars return
decoding errors", "arbitrary bytes decode without synchronous exceptions",
and "a zero denominator is skipped and unrelated definitions load".

**Export: the text form of a store.** `:export [ns] [file]` writes the
stored codebase, or the namespace `ns`, as source that `:load` reads back.
In a fresh session, `:load file` then `:add` gives the same labels on the
same hashes (`names`, `typeNames`, `conNames`, `fieldNames`, `units`,
`charts`, `signatures`). The rules of the text:

- Each namespace is a `namespace` block, nested as the paths nest, with
  root definitions outside any block.
- Each definition is rendered as `:edit` renders it: `let name = body`,
  `unit name = …`, `space Name = type`, `chart name params on parent` with
  its clauses (§3.8, §3.10), `data` declarations with their field names,
  and a signed definition's `name :: type` line just before it, spelled
  for its block, with its `forall` (§4.8).
- The standard library's namespaces are not exported unless one is asked
  for (`:export si`), because a codebase that reads the export is seeded
  with them already.
- The codebase's stored `use`s (§7.7) head the export as `use` statements,
  the six of a seeded codebase. Every name is spelled for them and for its
  block (§7.6). A library term that a user definition references prints
  as `km`. A name the block shadows gets its leading dot (`.km` for a root
  `km`), and so does a root name that a stored use also offers, since a
  `use` in a file comes before the root. So the text means the same in any
  codebase seeded with the library, whatever its stored uses.
- Types come first, each after the types it uses, since `data`
  declarations are entered in order. Then come the terms, each after what
  it references, a cycle's members together. Among the terms that are
  ready, the export takes the ones in the same namespace as the last
  first, so few blocks are opened again.
- `:export orbital` exports that subtree as `namespace orbital …`, so
  loading it elsewhere lands it in the same place. An empty codebase
  exports nothing. The pending scratch is not exported, and a closing
  comment (or, for a file, a note) says so.

These things do not round-trip, for these reasons:

- A definition that refers to a version no name points at (after `:update
  --no-upgrade` and an `:unname`) cannot be written as source, so the
  export refuses and names it.
- A definition with a `sample` and a nominal type are stamped with their full
  path (§3.2.4, §2.3). `:rename` and `:move` keep the stamp up to date by
  re-hashing (§7.2), but a definition whose stamp does not match its path
  (a second label on it) gives a new hash when its export is entered again.
- Two labels on one reference export as two definitions. They hash alike
  only when the body declares no `sample` and is not recursive, because the
  second refers to the first by name instead of being a member of its
  cycle.
- A type or constructor that a definition uses but no label names prints
  as a hash and does not read back.
- A library name that the user rebound or unnamed under its namespaces is
  not exported with the rest. `:export si` writes that part as the
  codebase has it, which needs `:update` rather than `:add` where it
  differs from the seed.
- History, preferences and the session's `use`s are not part of the
  export.

So for iapetus the binary `.metron/` store is the source of truth for
history and hashes, and an export beside it is the reviewable text,
diffable in git and enough to rebuild the current labels.

**Seeding.** The standard library lives in the store like everything else
(§7.7). A store that does not exist yet is created and seeded. The
library's terms are written, then its labels as ordinary `bind`, `unit`
and `chart` lines and its six stored `use`s, all stamped with time `0`.
Time 0 sorts before every line of the user's, so a merge can never let the
seed override the user. The seed's lines are the same in every store, so
merging two seeded stores brings nothing across for the library. The
format file is written last, so an interrupted seeding is seeded again. A
store is then loaded on top of the empty codebase, with no prelude step:
an empty store really is empty, and the second start of a new store reads
the library from disk. `--no-codebase` seeds the same library in memory.

**Writing through.** Each successful input is written at once: new terms
first, dependencies before dependents, then the log lines, so an
interrupted session never leaves a name pointing at a missing term. On
load, a term that fails to decode, fails to typecheck, or is named but
missing is reported as a note at start and skipped, and the rest loads.

**Formats.** A store opens only at the format this build writes, 12. A
store of another format is refused with one line, and nothing in it is
touched: "<path>: this codebase is format N; this metron opens format 12".
A format file that says anything else is refused as not a metron codebase.
**Decided.** There are no migrations: hashes can change between builds,
and a store of an older format is recreated, from its export where the
user has one.

**Implemented in:** `Metron.Store` (`formatVersion`, `locateStore`, `openStore`, `seedStore`, `loadStore`, `sync`, `mergeStore`, `mergeStores`, `stdlibSeed`), `Metron.Hash` (`encodeStored`, `decodeStored`), `Metron.Source` (`exportSource`, `exportRequest`), `Metron.Driver` (`seededSession`). The command line is `src/Main.hs`.
**Tested by:** "store" › "definitions, history, units, labels and cycles survive a reload", "a store of another format is refused with one line and left as it is", "merging two stores: both sides' definitions, one file per shared term", "metron --merge says what came across, and refuses with one line and a failure", "merging two seeded stores brings nothing across for the library", "a corrupt term file and a dangling name are reported, the rest loads"; "namespaces" › ":export reads back to the same labels and hashes", ":export refuses a definition on a version no name points at"; "type annotations".

### 7.5 Scratch, add, update, upgrade

The codebase is never written by typing a definition. This follows
Unison, whose users edit a scratch file that the codebase manager
typechecks on every save, and then run `add` or `update` to store what
checked. The separation makes versioning deliberate: trying a definition
and committing a version are different acts.

- **Scratch.** Every `let` from the REPL or a file goes into the scratch.
  The whole scratch is entered on top of the codebase as one binding group
  (§6.3) after each change. So errors appear at once, and expressions see
  scratch definitions first, then the codebase. A file that defines a name
  twice is an error. A later REPL input that defines a *pending* name
  again replaces it with a notice, because the scratch is a workspace, not
  a scope.
- **The scope of a pending definition.** A pending definition is known by
  its full path and keeps the scope it was written in: its namespace and
  the `use`s then in effect (§7.6). So entering the scratch again resolves
  it as it did. After `:namespace orbital`, `let x = 1` is `orbital.x`.
  `:scratch`, `:todo`, `:add` and `:update` print names as the current
  scope spells them (§7.6), so it shows as `pending: x` there and
  `pending: orbital.x` at the root.
- **Pending signatures.** A signature (§4.8) is a pending entry of its own
  beside its definition's, `pending: area :: Shape -> Num (m^2)`. A later
  input's signature replaces it (``replaced pending signature of `area` ``),
  a later `let area` is checked against it, and `:forget area` drops both.
  `:add` or `:update` stores a pending signature for a stored definition
  alone, and reports `signed area`.
- **`:add`** stores pending definitions whose names are new, or whose
  definition is unchanged. A name that exists with a different definition
  is a conflict, and the message points at `:update`.
- **`:update`** stores pending definitions, binds names that already exist
  again, and then **propagates**. Every current definition whose term
  mentions an old reference is rewritten to the new one (`Ref old` becomes
  `Ref new`, a pure rewrite on Core), hashed again, stored, and its names
  bound again. Propagation runs in dependency order, so each dependent is
  rewritten once, and it handles cycles, since a cycle is one term. Each
  rewritten dependent is typechecked again against the codebase. One that
  no longer checks stays on the old version, and the report gives the
  reason (`left g on #k2: expected Num -> Num, got Num`). `:update
  --no-upgrade` binds again without propagating.
- **`:upgrade name`** is propagation on demand: every dependent that still
  refers to a historical version of `name` moves to its current version,
  where it checks.
- **`:todo`** lists pending definitions and stale references, so nothing
  is forgotten.
- **`:edit`** opens a definition, a namespace or the codebase in an editor
  and reconciles the saved file with the codebase (§7.3): it adds, updates
  with propagation, and removes. Without an editor it prints the source.
- **`it`**, the last expression (§7.3), is never stored. It is not in the
  scratch, so `:add` and `:update` do not see it, and nothing reaches the
  codebase or the store through it. A definition that mentions `it` is
  refused with "`it` is the last result and cannot be stored; paste its
  definition (:view it) instead", and so is a definition named `it`. `it`
  keeps the terms it was checked against, so replacing or forgetting a
  pending definition it used does not break it.

`:add`, `:update` and `:edit`, which does both from a file, are the only
ways a label moves to new content. History records every binding, `:view`
shows exactly which version a definition uses, and the propagation report
says what moved, what did not, and why.

**Implemented in:** `Metron.Driver` (`feed`, `add`, `update`, `upgrade`, `todo`, `forget`), `Metron.Update` (`propagateNamed`, `propagateScoped`, `staleReferences`), `Metron.Resolve` (`processGroup`).
**Tested by:** "codebase" › "redefining a pending name replaces it with a notice", ":update rebinds and upgrades dependents (design §7.5)", "upgrading propagates transitively and through cycles"; "it, the last result" › "it is never stored or listed"; "type annotations" › "the scratch lists a signature; :add stores it; :forget drops it".

### 7.6 Namespaces

A name is a dotted path, `orbital.kepler.period`, and nothing else
changes: a namespace is a prefix on a label. Terms, hashes and the store
do not see it, since a `Ref` carries only a hash and, in the storage
encoding, the name as written (the full path it resolved to). The one
exception is the owner stamp of a `sample` definition or a nominal type, which
is its full path (below). Moving `period` under `orbital` is a relabelling
(§7.2), so history keeps the old name and nothing is hashed again, unless
`period` is stamped. Types, constructors and fields are labels too and
move the same way, and so do the `unit` and `chart` flags. The standard
library's units and constants live in namespaces by domain (§7.7), and the
stored `use`s reach the common ones: `5 km` is `si.km`.

**Blocks.** `namespace` opens a block of statements, laid out as a `where`
block is (§2.2): it opens at the first token after the path, which must be
indented further than the `namespace` line. The block holds `let`,
`unit`, `chart`, `space`, `data`, `use`, signatures, expressions and
nested `namespace` blocks. What it declares gets its path as a prefix:
definitions, units, charts, spaces, types, constructors and record fields
alike.

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
dependency analysis and cycles work across them. Dependency analysis runs
on full paths: `period` inside `namespace orbital` depends on `orbital.mu`
when the group defines it.

**Resolution.** A name written in an expression, a type or a command
resolves in this order:

1. A local binder: a lambda parameter, a `let`, a pattern variable.
2. The current namespace. `period` inside `namespace orbital` means
   `orbital.period` when that exists, in the group or the codebase. An
   enclosing namespace is not searched, so inside `orbital.kepler` the
   name `mu` is not `orbital.mu`. Write that, or `use orbital`.
3. The `use`d namespaces: `u.x` for each `use u`, and `u.y` for `k.y`
   under `use u as k`. Two of them offering the name is an error, not a
   choice: "`x` is both `a.x` and `b.x`; write one of them".
4. The root, which is where every name without a dot lives.
5. The codebase's stored `use`s (§7.7), the six of a seeded codebase
   (`std`, `linalg`, `si`, `time`, `angle`, `temperature`), with the same
   rule against two of them offering the name.

A full path written out, `orbital.period`, resolves as itself at the root
step, so it works from anywhere unless a nearer namespace has the same
path under it. A leading dot writes an absolute name: `.km` is the root's
`km`, and `.orbital.period` is the full path, whatever is current or used.
At the root, step 2 is skipped. So a `use` of the session or a file takes
precedence over a root name of the same spelling, while a root name takes
precedence over a stored `use`. For example, `let c = 3e8 m/s` at the root
shadows the library's `physics.c` (after `:use physics`) without
ceremony, and `physics.c` still reaches the library's. Each kind of label
resolves among its own kind: definitions and constructors share one set,
and types and fields have theirs.

A `use` path is always a full path. A leading dot is allowed and means the
same. A `use` applies to the statements after it in its block and in the
blocks inside it. A top-level `use` typed at the REPL lasts for the
session (`:uses` lists them, `:unuse` drops one). A file read with `:load`
keeps its own to itself. Neither `namespace` nor a `use` statement is
stored: a stored term holds full references, so no reader of the codebase
needs imports to make sense of it. The one exception is the codebase's
stored `use` list, the six at seeding (§7.7), kept as log lines and
changed with `:use` and `:unuse`.

**The dot.** `b.mass` is a field access and `v.0` a projection, so
`orbital.period` lexes as "field `period` of `orbital`". The desugarer
decides (§2.10): for a chain whose head is not a local binder, the longest
dotted prefix that resolves to a definition or a constructor is a
qualified reference, and the rest is field access. That rule is
unambiguous because **a name is never both a label and a namespace**:

- Declaring `let orbital = …` while any `orbital.*` label exists is
  refused: "`orbital` is a namespace; a definition cannot have its name".
- Declaring anything under `period.` while `period` is a label is refused:
  "`period` is a definition; it cannot also be a namespace, as `period.x`
  would make it".

The rule covers labels of every kind. It is checked for a whole binding
group and for `:alias`, `:rename`, `:move` and `:namespace`, and it means
a namespace cannot be named like a definition (`namespace si.km` is
refused).

*Fields.* A field written after a dot is a bare name and resolves through
the scope only (`.mass` is `orbital.mass` inside `orbital`, or with `use
orbital`). From elsewhere, a field of a type in another namespace cannot
be written by path: `use` its namespace. A record built with a
constructor, `orbital.Body {mass = …, dist = …}`, takes its field names as
that constructor's own, by their last segment, from anywhere. Records
print their fields so.

**Stamps see the namespace.** A definition's declared uncertainties are
labelled (§3.2.4) with its full path, and a nominal type is stamped (§2.3)
with its full path. So `lab.offset = sample (normal 1 0.1)` and `field.offset = sample (normal 1 0.1)` are two terms and two measurements, `lab.offset - field.offset`
carries both sampled inputs, and `a.Body` and `b.Body` with the same fields are
two types. Everything else is the same term wherever it is written: `let q
= 1 m` has one hash at the root and in any block. The cost: renaming or
moving a stamped definition hashes it again, which `:rename` and `:move`
do (§7.2), and the library's `astro.G` is not the hash that a root `G` of
the same text has.

**Printing.** A name prints as Unison prints it: the shortest spelling
that resolves back to the same label in the current scope. The printer
tries, in order:

1. the last segment alone
2. the path relative to the current namespace
3. the path relative to each `use`, under its alias (`k.anomaly`), the
   session's first, then the stored ones
4. the full path
5. the absolute `.full.path`, only when the full path itself resolves to
   something else here

So inside `namespace orbital` with no `use` of the session,
`orbital.period` prints `period` and the library's `si.km` prints `km`.
With `use orbital` at the root, `orbital.period` prints `period`. With
`use a` and `use b` both offering `x`, `a.x` prints `a.x`. A block that
defines its own `km` refers to the library's as `si.km`, and to a root
`km` as `.km`. After `:unuse si`, `5 si.km` prints `5 si.km`. At the root
with no `use` of the session, every root name prints as itself, and so
does every library name that no root name shadows. The rule is used for
`:view`, `:edit`, `:core`, values and their units, types and constructors
(through the type namer), `:ls` outside a namespace listing, `:names`,
`:dependents`, and the notes `pending:`, `added`, `updated`, `upgraded`,
`left` and `stale:`.

**Commands.** A namespace is an object: wherever a command takes a name, a
namespace path means everything under it, and the command says how many
labels it touched. Names given to commands are relative to the current
namespace, go through the `use`s, or are absolute with a leading dot (but
`:unname .f` names the field `f`).

```
:namespace orbital           -- single REPL lines land under orbital; :namespace . is the root
use orbital as o             -- for the session; :uses lists, :unuse orbital drops it
:ls orbital                  -- the namespace's labels, relative to it, data lines included
:rename orbital.period orbital.T    -- one label: renamed `orbital.period` to `orbital.T`
:rename orbital mechanics    -- every orbital.* label of every kind: renamed the 5 labels under …
:move period orbital         -- period becomes orbital.period; :move orbital.kepler mechanics
                             -- gives mechanics.kepler.*
:alias o2 orbital            -- every orbital.* label also as o2.*
:unname orbital              -- removed the 5 labels under `orbital`; :history name still finds them
```

`:rename`, `:move` and `:alias` of a namespace are all or nothing. Each of
these refuses the whole change: a new path that is already a label of the
same kind ("`x` is already a label; nothing was changed"), two names moved
to one path, or a path that breaks the namespace rule. They are written to
the store as the existing `bind`, `unname`, `type`, `con`, `field`, `unit`
and `chart` log lines, beside the new term and type files of anything
re-stamped (§7.2). `:edit` of a definition outside the current namespace
prints it inside a `namespace` block, with its names relative to that
block, for pasting at the root.

**Open.** How much of the tree `:ls` shows, and whether a field can be
reached by path from outside its namespace (§11).

**Implemented in:** `Metron.NameResolution` (`resolverFor`, `shortestName`, `qualifyName`, `namespaceLabels`, `isNamespace`, `disjointness`), `Metron.Session.Names` (`relabel`, `removeLabel`, `argPath`), `Metron.Desugar` (`desugarDefinition`), `Metron.Update` (`restamp`).
**Tested by:** "namespaces"; "standard library" › "units resolve through the stored uses and print bare", "a root name shadows the library's: c and physics.c".

### 7.7 The standard library

The standard library lives in the codebase like everything else.

- **Seeding.** A codebase that does not yet exist is created with the
  standard library entered as one ordinary binding group of sibling
  `namespace` blocks, one per domain (the layout below: `std.map`,
  `linalg.cross`, `si.km`, `time.hr`, `temperature.degC`, `astro.G`, …).
  Its source is `Metron.Prelude.stdlibSource`. The second labels on one
  term (`Metron.Prelude.stdlibAliases`: `si.newton` on `si.N`'s term,
  `time.h` on `time.hr`'s) are then bound as `:alias` binds them, and an
  alias of a unit is a unit. The terms and the `bind`, `unit` and `chart`
  lines are written like any other, with six stored uses: `std linalg si
  time angle temperature` (§7.4 gives the store's side: the seed's lines
  are at time 0). The second start reads the library from disk, and
  nothing is entered in memory first. `--no-codebase` seeds the same
  library in memory.
- **A definition is the term it is written as,** wherever it lives:
  `si.N`, `time.min` and `std.map` are the terms that `N`, `min` and `map`
  are at the root, and `si.km`, written `kilo * 1 metre`, has its own. A
  definition with a `sample` is stamped with its full path (§3.2.4). So
  `astro.G`, the bodies of `astro.iers2010` and `astro.wgs84.earth` (its
  J2), and the solvers of `astro.kepler`, which declare their truncation
  error, have hashes of their own too.
- **Nothing is special afterwards.** The library is names in the
  database. `5 km` resolves through the stored `use si` and prints `5 km`.
  `:ls` alone lists the root's own names and one line per namespace,
  `namespace angle (6 names)` to `namespace time (12 names)`, sorted. `:ls
  si` lists the SI, and `:ls --all` everything by full path. After `:use
  physics`, `let c = 3e8 m/s` shadows `physics.c` without ceremony, since
  a root name comes before a stored `use` (§7.6), and `physics.c` still
  reaches the library's. `:rename time.hr time.hour` (then `3 hour`),
  `:unname astro.AU` and `:edit si.km` all work. `:export` leaves the
  library's namespaces out, and `:export si` writes that one.
- **Stored uses.** A `use` statement lasts for the session (§7.6). The
  codebase also keeps a list of stored uses, the six from seeding, written
  as log lines (`<time> use si`, `<time> unuse si`) and replayed with the
  other labels. They resolve after the root, last of all, and two of them
  offering a name is an error, as for any uses. `:uses` lists them first,
  marked `(stored)`, then the session's. `:use path [as alias]` adds a
  stored use and prints `stored use path`. A `use` statement stays the
  session's. `:unuse path` removes a stored use when one matches the path
  or alias, and says so (`removed the stored use si; :use si puts it
  back`). Otherwise it removes the session's. A change to the stored uses
  is refused when the pending scratch no longer checks without it. After
  `:unuse si`, SI names need their path (`5 si.km`). After `:unuse
  linalg`, so does `×`, which is the library's `linalg.cross`.
- **`:stdlib upgrade`** compares the shipped library's labels in its
  namespaces against the codebase's:
  - A name the codebase has never had is `added`. So is a type,
    constructor or field label it has never had (`added data
    linalg.Cov2`, with its constructor and fields). A type label the
    codebase already has is left as it is.
  - A name whose binding is still the one it was seeded with (its history
    is that one entry), and whose shipped version differs, is `updated`,
    and its dependents are upgraded as `:update` does.
  - A name the user rebound or unnamed is `kept`: the user's wins.
  - With nothing to do it prints `the library is up to date`.

  "Never touched" is read off the history, because the codebase does not
  know which versions earlier libraries shipped. So a name moved by an
  earlier upgrade counts as the user's. `--merge` is the wrong tool here,
  because its last-writer rule overrides the user's edits. **Open.**
  Upgrading a codebase from a newer library or from another codebase in
  general (§11).
- **Base units are primitives.** `m`, `kg`, `s` and the other base symbols
  are not names (§3.2.12). They need no namespace, cannot be renamed, and
  are available everywhere. `si.metre` and the other spelled-out names are
  units defined as them (`unit metre = m`), and the prefixed units are
  written from these.
- **One library.** Only the current library is in the build.
- **The built-in types.** `std` begins with `structural data Bool = False
  | True`, `structural data Pair a b = Pair a b` and `structural data List
  a = Nil | Cons a (List a)`, written exactly as the compiler holds them
  (§2.3). So entering them gives the compiler's hashes: `std.Bool` is the
  type of `true`, and `:view std.List` prints the declaration. The labels
  only name them: `true`, `(1, 2)` and `{1, 2}` print by hash. So renaming
  or unnaming `std.Bool` changes how `Bool` is named in `:view` of a
  declaration and nothing else, and the language works the same in a
  codebase without them. Under the stored `use std`, `True`, `Pair 1 2`
  and `Cons 1 Nil` are the constructors. The larger tuples' types (`(a,
  b, c)`) are known to the compiler but named by no library.
- **Hashes follow the source.** Changing how the seed writes a definition
  (`km` as `kilo * 1 metre`, the hour as `60 min`) changes its hash.
  **Decided.** This is accepted while the language is in design: a store
  of an older format is refused and recreated from its export (§7.4).

#### Layout

The library is split by domain into sibling namespaces, each a `namespace`
block in the seed source, with the basic functions alone in `std`. The
counts are labels, as `:ls` counts them (aliases and record fields
included, and a nested block's labels counted in its top namespace), 981
in all:

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

A test checks each of these rules:

- No name is ambiguous among the six default-used namespaces, for each
  kind of label.
- A name only in a namespace that no stored use reaches (`astro`,
  `physics`, `imperial`: `AU`, `G`, `c`, `planck`, `g0` and the rest) is
  not bare.

Both hold for the nested blocks of `astro` too: `earth`, `period` and
`Elements` are not bare until `:use astro.wgs84` or `:use astro.kepler`.
Base units are primitives, available everywhere, and a `data` type's
dimension (`Num N`) names a unit through the scope like any expression.

The choices the layout makes:

- **Two left folds, as Haskell has.** **Decided.** `std.foldl` is lazy in
  its accumulator: `foldl (\_ x -> x) (1/0) (range 0 3)` is `3`, and an
  accumulator that is never used never fails. `std.foldl'` evaluates each
  step's accumulator before the next, through the primitive `seq a b`.
  `seq a b` gives `b` once `a` is evaluated to a value and, for a number,
  a tensor or a point, every component (data only to its constructor). A
  component that fails keeps its error to itself, as elsewhere (§3.3):
  `seq [1/0, 2] 5` is `5`. `length` and `reverse` are written with
  `foldl'`, so `length (range 0 1e6)` runs in constant memory. `seq` is in
  tail position, so a strict fold also runs in constant stack. `'` is an
  identifier character, so the name is spelled as in Haskell.
- **`kelvin` is the absolute temperature scale** (`0 kelvin to degC`). So
  `K` has no spelled-out unit name in `si`: a name is one label, and two
  default namespaces that offer `kelvin` are an error. The prefixed
  kelvins are written from the symbol (`unit mK = milli * 1 K`).
- **`in` is a keyword**, so the inch is `inch`.
- **The prefixes are powers of ten** (`kilo = 10^3`), not literals. A term
  is its content, so `let kilo = 1000` has the same hash as a user's `let
  n = 1000`, and an `:update` of that upgrades every `k` unit with it
  (§7.5).
- **The hour is `hr`, with `h` its alias,** and `physics.h` is Planck's
  constant. Both spellings of the hour work bare by default (`3 h`, `5
  km/hr`), each printing as written. After `:use physics`, a bare `h` is
  the usual ambiguity error, "`h` is both `time.h` and `physics.h`; write
  one of them", and `hr` is the way out. The quantity rule lets an
  ambiguous name through, so that this error, not "not a unit", is the one
  reported.
- **`physics`'s defining labels are the long spellings** (`planck`,
  `k_B`, `N_A`, `e_charge`), and the short ones are aliases. The atomic
  mass unit `u` is not shipped.
- **`g0` is in `physics`**: standard gravity is a constant. There is no
  gauge-pressure chart (§3.10, F2).
- **References between blocks** are written by path (`angle.sr` in `lm =
  cd * angle.sr`, `physics.c * time.year`, `mile / time.hr`) or through a
  `use` inside the block (`physics` has `use si`), since the seed is
  entered before any stored use exists.

#### The `astro` library

**Decided.** `astro` is a library of nested namespaces, so that a user
chooses a set of constants with a `use` and the functions do not depend on
the choice.

- **Constant sets are namespaces that define the same names.** A set holds
  `Body` values (below), and each value says its source in a comment and
  in its `:view`:
  - `astro.wgs84`, the WGS84 and EGM96 Earth that GPS and Vallado use:
    `earth`
  - `astro.iers2010`, the IERS Conventions (2010): `earth`, `moon` and
    `sun`
  - `astro.iau2015`, the IAU 2015 nominal values (Resolution B3): `earth`,
    `sun` and `jupiter`, exact by definition
  - `astro.de440`, JPL DE440: `sun`, `moon` and the planets

  `:use astro.wgs84` then makes `earth` the WGS84 Earth. Defining
  constants are exact, and measured ones carry their published
  uncertainty with normal distributions. No set is used by default.
- **A body is a record:** `data Body = Body {mu :: Num (m^3/s^2), radius
  :: Num m, flattening :: Num, j2 :: Num, rate :: Num (rad/s)}`, with an
  exact zero where a source gives nothing. Every function that needs a
  body takes one, `period earth (7000 km)`, so a computation names its
  constants once and changing set is a `use`.
- **`astro.kepler`, two-body motion:**
  - relations: vis-viva, period, mean motion, specific energy, angular
    momentum, and circular and escape speeds
  - `data Elements = Elements {a, e, i, raan, argp, nu}`, elliptic or
    hyperbolic (`a < 0`, as Vallado writes it), with conversions to and
    from a position and velocity, including the circular and equatorial
    cases. Angles come from `atan2`, never from `acos` with a quadrant
    test. A case that cannot be decided because the value is too uncertain
    is an error.
  - anomaly conversions: true, eccentric, mean and hyperbolic
  - a Kepler solver for each conic
  - analytic propagation, by advancing the mean anomaly, and the J2
    secular rates: the node, the perigee, and the sun-synchronous
    inclination
- **Solvers evaluate every realization.** Fixed Newton iterations propagate
  sampled inputs. Tests check residuals and published examples.
- **`astro.maneuver`:** Hohmann, bi-elliptic, plane change, combined plane
  change and phasing, returning `Transfer` records.
- **The root `astro`** holds the units `AU`, `pc` and `ly`, `G`, the
  `State` record, `velocityIn` and `stateFrom` (§3.8). The Earth and Sun
  constants are in the sets.
- **Tests.** Every function is checked against a published worked
  example, cited (Vallado's *Fundamentals of Astrodynamics and
  Applications*, examples 2-1 to 2-6 and those of chapter 6, or Curtis),
  and the conversions round-trip.

Two pieces of the language serve this library (§2.5, §3.10): `x to a to
b` chains from the left, and `pointAt : Chart c -> Diff c -> Point c`
places a computed amount on a chart from its origin, in place of `[0, 0,
0] c .+ withAxes c v`.

**Nesting.** The seed's `astro` block holds nested `namespace` blocks, so
the sets are `astro.wgs84.earth` and so on, and the checks of the layout
cover them. An enclosing namespace is not searched (§7.6), so the inner
blocks say `use astro` to read a body's fields, and a user does too:
`earth.mu` needs `:use astro`, because fields resolve through the scope
only, while `period earth (7000 km)` needs only `:use astro.kepler` and a
set. Two sets used at once make `earth` ambiguous. `:ls` counts a nested
block's labels in its top namespace, `namespace astro (91 names)`, and
`:ls astro` lists them by their path under it, `wgs84.earth : Body`.

**The constants**, each cited beside it in `Metron.Prelude`. A defining
constant is exact. A measured one uses a normal distribution with its published
standard uncertainty. The table gives mean and standard deviation as a pair. A
field that a source does not define is an exact zero.

| set | body | value | source |
|---|---|---|---|
| `astro` | `G` | `6.67430e-11, sd 1.5e-15 m³ kg⁻¹ s⁻²` | CODATA 2018 = 2022 (NIST) |
| `wgs84` | `earth.mu` | `3986004.418e8 m³/s²`, exact (defining; eq. 3-3 quotes 1σ `0.008e8`) | NIMA TR8350.2 3rd ed., eq. 3-3, Table 3.1 |
| | `earth.radius` | `6378137 m` | TR8350.2 eq. 3-1, Table 3.1 |
| | `earth.flattening` | `1 / 298.257223563` | TR8350.2 eq. 3-2, Table 3.1 |
| | `earth.j2` | `−√5 C̄20`, `C̄20 = −0.484165371736e-3, sd 0.35610635e-10` (tide-free, 1986.0) | EGM96, NASA/TP-1998-206861 App. C; TR8350.2 eq. 7-1, Table 5.1 |
| | `earth.rate` | `7292115e-11 rad/s` | TR8350.2 eq. 3-6, Table 3.1 |
| `iers2010` | `earth.mu` | `3.986004418e14, sd 8e5 m³/s²` (TCG) | IERS TN36 Table 1.1 |
| | `earth.radius` | `6378136.6, sd 0.1 m` (zero tide) | TN36 Table 1.1 |
| | `earth.flattening` | `1 / (298.25642, sd 0.00001)` (zero tide) | TN36 Table 1.1 |
| | `earth.j2` | `1.0826359e-3, sd 1e-10` (zero tide) | TN36 Table 1.1 |
| | `earth.rate` | `7.292115e-5 rad/s`, exact (Table 1.1 has none) | TN36 Table 1.2 (GRS80 nominal) |
| | `moon.mu` | `(0.0123000371, sd 4e-10) × earth.mu`; other fields 0 | TN36 Table 1.1, the Moon-Earth mass ratio |
| | `sun.mu` | `1.32712442099e20, sd 1e10 m³/s²` (TCB) | TN36 Table 1.1 |
| | `sun.j2` | `2.0e-7`, exact (adopted for DE421); radius, flattening, rate 0 | TN36 Table 1.1 |
| `iau2015` | `earth` | `mu = 3.986004e14 m³/s²`, `radius = 6.3781e6 m`, `flattening = (6.3781e6 − 6.3568e6) / 6.3781e6` (derived from R_e, R_p); j2, rate 0 | IAU 2015 Resolution B3 |
| | `sun` | `mu = 1.3271244e20 m³/s²`, `radius = 6.957e8 m`; others 0 | Resolution B3 |
| | `jupiter` | `mu = 1.2668653e17 m³/s²` (without the Galilean satellites), `radius = 7.1492e7 m`, `flattening = (7.1492e7 − 6.6854e7) / 7.1492e7`; j2, rate 0 | Resolution B3, Explanation 8 |
| `de440` | `mu` (km³/s², TDB, exact: no σ published) | `sun 132712440041.279419`, `mercury 22031.868551`, `venus 324858.592`, `earth 398600.435507`, `moon 4902.800118`, `mars 42828.375816`, `jupiter 126712764.1`, `saturn 37940584.8418`, `uranus 5794556.4`, `neptune 6836527.10058`, `pluto 975.5` (Mars to Pluto: the systems) | Park et al. 2021, AJ 161:105, Table 2 |
| | radius, j2 | `earth 6378.1366 km, 1.08262539e-3`; `moon 1738 km, 2.03214360135e-4`; `sun 696000 km, 0.219613915165298248e-6`; others 0; no flattening or rate | `header.440` (RE, J2E, AM, J2M, ASUN, J2SUN) |

**The solvers.** Elliptic and hyperbolic Kepler solvers perform twelve Newton
steps per realization. Their starters are `M + e sin M` and
`asinh (M / (e − 1))`. The parabola uses Barker's closed form.
The result carries all sampled input realizations. No hard residual bound
is attached. Tests compare published examples and inverse-equation residuals.

**`fromState`'s cases** compare each realized eccentricity and node vector
with zero. Approximation can make a mathematically circular orbit slightly
eccentric. The code does not apply an implicit tolerance.
The record keeps its shape in each case:

- circular: `argp = 0`, and `nu` is the argument of latitude
- equatorial: `raan = 0`, and `argp` is the longitude of periapsis
- both: both zero, and `nu` is the true longitude

Angles are in `[0, 2π)`, as Vallado gives them, through `fullAngle`,
`π + atan2 (−y) (−x)` with an exact zero on the positive x axis. A
hyperbola's anomalies are in `(−π, π)`. `toState` writes the perifocal
axes directly in sines and cosines.

**`maneuver`'s** burns are signed (after less before), and a `Transfer`
has three, `dv3 = 0` for two-burn transfers. A namespace cannot have two
records with a field of one name, so one record serves.

**Open.** The second build of `astro` (§10): time (TAI and GPS charts, leap
seconds, GMST and the Earth rotation angle), frames (`GCRS`, a moving
`ecef`, ENU and SEZ, perifocal, LVLH and RSW) and geodesy (WGS84 geodetic
coordinates, azimuth, elevation and range), then Lambert.

**Implemented in:** `Metron.Prelude` (`stdlibSource`, `stdlibAliases`, `stdlibDefaultUses`, `stdlibNamespaces`, `stdlibCodebase`, `isLibraryPath`), `Metron.Store` (`stdlibSeed`, `seedStore`), `Metron.Driver` (`seededSession`, `stdlibUpgrade`), `Metron.Codebase` (`addStoredUse`, `removeStoredUse`).
**Tested by:** "standard library"; "prelude"; "astro (design §7.7)" › "constant sets", "relations", "elements and states", "anomalies and Kepler solvers", "propagation and J2", "manoeuvres"; "limits (design §8.1)" › "constant memory" › "foldl stays lazy in its accumulator; foldl' evaluates it".

## 8. Evaluation

The evaluator is an environment-passing interpreter over **Typed Core**
(§5.3). It never sees surface syntax or an unresolved overload. Its
type-error cases are unreachable for linted terms, and it reports them as
internal errors.

- **Values** are the runtime forms of §3.1. A tensor of any rank is one
  runtime shape: a flat row-major buffer of element thunks beside its list
  of lengths, with a dimension vector and a display hint. A number is the
  rank-zero case, a buffer of one element. A projection is an O(1) slice,
  and elementwise arithmetic is a zip over the buffer. A component that
  fails to evaluate is a failing element, so an error surfaces only when
  that component is used. The buffer is boxed because its elements are
  scalars of the backend (§8.2): rational or double values with optional input and rounding realizations.
- **Type forms are erased**, except where a value's runtime shape or
  dimension comes from a type alone: the element type of an empty tensor
  literal, and the instantiated type of `vmap`, `vzipWith` and `timap`,
  which gives their result's dimension (§3.3). An abstraction over a
  length, shape or dimension variable that its body needs there, or passes
  on in a type application, waits for its argument. Each application
  supplies it, resolved under the arguments in force where it is written,
  and closures capture those arguments. Every other abstraction evaluates
  its body once, shared by all its applications, so a polymorphic value is
  not recomputed per use. A variable that nothing applies, at the top of
  an expression or never used, is unconstrained, and the evaluator takes
  any instance of it (an empty shape, length zero, dimensionless). The
  prompt refuses a value whose type leaves one open (§3.3), so such an
  instance never prints.
- **No dispatch on values.** A monomorphic `PrimApp` is a direct call with
  its arguments as thunks, forced as the primitive needs them. There is no
  dispatch on value tags and no arity bookkeeping. The type checker
  guarantees that shapes and dimensions match, so the evaluator checks no
  dimension and only maintains the vector for printing. Typed Core has no
  dictionary forms: every overload is resolved or defaulted before
  evaluation (§4.2).
- **Call by need.** Closures capture the environment, and application is
  call by need: Haskell's own laziness supplies the thunks, which `case`
  and recursion rely on. Errors are values, not exceptions.
- **A long run keeps only what it still needs.** These rules hold so that
  a loop runs in constant memory and constant stack:
  - a call in tail position is a Haskell tail call, so `let loop n = loop
    n` runs in constant stack until `steps` stops it.
  - an argument that is a variable is the thunk it is bound to, not a new
    thunk around the environment, and a literal is built at once.
  - a closure keeps only the variables free in its body. A function term
    (`TLamWith`) carries that set, computed once, and the closure takes it
    when it is built.
  - a value's shape, dimension and display unit are strict fields,
    evaluated with the value, and so are a magnitude's rationals.
  - a call evaluates first the arguments its function certainly evaluates
    (`Metron.Strictness`). A `case` evaluates its scrutinee and what every
    alternative evaluates, a strict primitive its operands, and a
    saturated call of known signature the arguments it is strict in. The
    members of a cycle are solved together, starting from "strict in
    everything". A function passed as an argument has no known signature,
    so `foldl f z` stays lazy in `z`. An argument evaluated early is
    evaluated with its components when it is a number, or a tensor or
    point of at most 64 components. A larger tensor's components stay
    lazy. Because errors are values, evaluating an argument early raises
    no error that the program does not raise anyway. A component that the function
    never reads is computed anyway, or, if it never finishes, stops at
    `steps`.
  - `seq a b` is `b`, once `a` is evaluated to a value and, for a number,
    a tensor or a point, every component (data only to its constructor). A
    component that fails keeps its error to itself: `seq [1/0, 2] 5` is
    `5`. `std.foldl'` is written with it (§7.7), and `length` and
    `reverse` use `foldl'`.
- **Data.** `Con` builds a data value whose fields are thunks. `Case`
  forces its scrutinee to a constructor and binds the fields, unevaluated,
  in the chosen alternative. Booleans are the two nullary constructors.
  Lists are cons cells of thunks, so an infinite `range` is fine until
  something walks it.
- **Recursion.** `Cycle` is evaluated by knot-tying: the list of member
  values is defined in terms of itself.
- **References.** `Ref` looks up the Typed Core of the referenced hash,
  elaborating it on demand, and evaluates it in the empty environment,
  memoised per session. A definition's value is shared by every reference
  to it in one evaluation.
- **Parameters, not globals.** Arithmetic, sampling, precision and resource
  limits are evaluation parameters passed through `Config`.
- **Elementary functions.** Rational kernels use precision-controlled
  approximations. Double kernels use libm and optional diagnostic perturbations.
- **Linear algebra.** Scalar implementations provide per-realization matrix
  kernels. Pivoting never discards a sampled input.

**Open.** A compiler from Typed Core, with explicit dimension and length
arguments telling it static shapes (§10).

**Implemented in:** `Metron.Eval` (`evalClosed`, `evalAt`, `evalDefinition`, `apply`, `evaluated`, `neededAtRuntime`), `Metron.Strictness` (`strictify`, `signatures`), `Metron.TCore` (`TLamWith`, `freeIndices`), `Metron.Compile` (`runtimeWith`).
**Tested by:** "evaluation" (for example "if is lazy in the untaken branch", "projection is lazy in the other components", "mutual recursion through a cycle: even and odd"); "limits (design §8.1)" › "constant memory"; "end to end" › "an empty tensor takes its element type from context".

### 8.1 Resource limits

A program can ask for more than a machine has: a huge exact number
(`2^(2^64)`, `1e1000000000`), recursion with no base case, an enormous list
(`range 0 1e9`), a vast tensor. **Decided.** Each such program fails as an
ordinary error that names the limit it hit, never by exhausting the
machine. A limit is a run-time setting with a default that a normal
session never reaches. A limit is a property of the session, not of a
term: it never changes a value or a hash, only whether an evaluation
finishes. Precision (`:set precision`) is separate, because it is a
property of the result.

| setting | default | what it bounds and where it is checked | the error |
|---|---|---|---|
| `memory` | 4 (GB) | the runtime's maximum heap, `RtsFlags.GcFlags.maxHeapSize`, set at startup and whenever the setting changes. The collector reads it at every collection, so a change takes effect at once. The runtime throws `HeapOverflow` to the main thread, which in the executable is the one that evaluates. It is caught around each input, the input's outputs are forced inside the handler, and a collection frees what the input built. | `error: the evaluation needed more than 4 GB (`:set memory`)` |
| `steps` | 10⁸ | evaluation steps per path of an expression: every reduction counts against the path it is on (steps per path, below) | `error: the evaluation took more than 100000000 steps (`:set steps`)` |
| `depth` | 10⁵ | nesting: one level for each value something waits for (an operand, a scrutinee, the function of a call, a thunk when forced). A call in tail position is no deeper. | `error: the evaluation nested more than 100000 calls deep (`:set depth`)` |
| `digits` | 10⁵ | a number's magnitude, its decimal exponent either way: `log₁₀` of its size from the leading bits of its numerator and denominator. Checked *before* computing where the size can be predicted: a power from its exponent (`n · log₁₀ |x|`), a literal in the lexer from its exponent, an exponential (`exp`, `sinh`, `cosh`) from its argument. Checked *after* every result of `+ − * /`, `outer` and `dot`. | `the literal would have more than 100000 digits (`:set digits`)`, `error: the power would have more than 100000 digits (`:set digits`)`, `… zeros after the point` for a small one |
| `components` | 10⁷ | a tensor's components, where a tensor is built: literal tensors, a stack of tensors, `outer`, `dot`, a matrix from a vector. A length that a type or a literal names has the fixed bound 2⁴⁰ instead, so that a definition checks the same in every session. A list's length is not known until it is walked, so `steps` and `memory` bound a list. | `error: the result would have 16000000 components, more than 10000000 (`:set components`)` |
| `outcomes` | 1000 | the options of one mixture under the double backend's samples (§8.2.6), when it is made and when it is printed | `the value would have more than 1000 outcomes`, `the value has more than 1000 outcomes` when printed |
| `time` | off | wall-clock seconds per input (a line at the prompt, a `-f` file, a `:load`), by `System.Timeout` around the input | `error: the input took more than 2 seconds (`:set time`)` |

`:set` lists the limits after the other settings. `:set NAME VALUE` changes
one, and `metron --set NAME VALUE`, given any number of times, starts a
session with one changed. A value is a positive whole number, written
`100000000`, `100_000_000` or `1e8`. `time` also takes `off`. Anything else
is refused, for example "steps is a positive whole number, such as 1000000
or 1e6". Each limit, when hit, is an ordinary error that ends with the
setting to change, and the session goes on.

Some details of where a limit applies:

- The executable links with `-rtsopts`. `--set memory` supersedes `+RTS
  -M`.
- A literal is checked against the session's `digits` at the prompt, in
  files, and in `:type`, `:view` and the other commands that evaluate.
  `:edit` and `:prefer` parse with the default `digits`.
- A Haskell stack overflow is caught too and named `depth` ("the
  evaluation nested too deeply"), but the stack is heap, so `memory`
  usually stops it first.
- Under threads (§8.2.7), a timeout or a heap overflow reaches the waiting
  thread and the batches are stopped. `runLimited` runs masked and takes
  in any further heap overflow after the first, so the session reports
  `:set memory` once and goes on to the next input.
- The test suite measures memory on its main thread before the tests
  start, because the runtime throws a heap overflow to the main thread and
  tasty runs a test on another.

**How the budget is counted.** The evaluator is pure and its values are
lazy thunks, so the counters live in place: `newBudget` makes the counters
of one evaluation (in `Compile.runtimeWith`), the nominal path's steps and
the nesting among them, and each group of copies that a split makes has a
counter of its own, its path's steps. `spend` and `nested` read and write
them with `unsafeDupablePerformIO`, `NOINLINE` and an argument that makes
each call its own. A limit reached is a `Left`, an `EvalError` like any
other, so `feed` stays pure and the tests see it. Only `memory` and `time`
need `IO`, in `runLimited`.

**Combined work and path budgets.** **Decided.** Before execution, the compiler
divides `steps` by the planned number of realizations, including the ordinary
baseline and every rounding repetition. It refuses a grid larger than the
step budget. Each branch path then uses this conservative per-realization
budget. Groups begin at their parent's count; a join takes the largest group
count. Work shared before a split is charged on every continuing path.
This can refuse an evaluation that would fit a precise total-work counter.

The grid is also limited to one million realizations and to `components`.
Input-only double batches use stable global indices; grouped rounding currently
runs as one bounded grid. `cores` does not change those coordinates.
The `memory` and `time` limits remain independent safeguards.

**Open.** Lazy values made before a split can be forced by different groups.
Their accounting can depend on the forcing order near a step limit. A shared
total-work model and chunked grouped execution need a separate design.

**Defaults.** `steps` is 10⁸, `depth` is 10⁵, `digits` is 10⁵,
`components` is 10⁷ and `memory` is 4 GB. These are resource ceilings,
not accuracy guarantees or expected running times.

**Examples.** Each runs at the defaults and fails at once with its limit,
except where noted:

```
> 1e1000000000
the literal would have more than 100000 digits (`:set digits`)
> 2^18446744073709551616
error: the power would have more than 100000 digits (`:set digits`)
> exp 1000000
error: the exponential would have more than 100000 digits (`:set digits`)
> let g n = if n == 0 then 0 else 1 + g (n - 1)
> g 1000000
error: the evaluation nested more than 100000 calls deep (`:set depth`)
> let f n = f (n + 1)
> f 0                          -- after about 5 s, in constant memory
error: the evaluation took more than 100000000 steps (`:set steps`)
> length (range 0 1e6)         -- in constant memory
1000001
```

**Limits and numerical reliability.** Resource limits bound work and storage.
They do not certify numerical accuracy. Chaotic iterations can be sensitive
to small perturbations while remaining finite.
Large exact rationals, retained lists and sample grids can exhaust memory.
The component limit counts tensors. Steps and memory also constrain lazy lists.

**Implemented in:** `Metron.Limits` (`defaultLimits`, `setLimit`, `parseCount`, `limitSettings`, `newBudget`, `spend`, `nested`, `enter`, `within`, `reach`, `log10Abs`, `beyond`, `runLimited`, `applyMemory`, `limitHeap`), `Metron.Eval` (`perOption`, `settle`), `Metron.Compile` (`runtimeWith`), `Metron.Driver` (`setSetting`, `startSettings`).
**Tested by:** "limits (design §8.1)" › "settings", "steps", "depth", "digits", "memory", "time", "constant memory"; "end to end" › "a tensor past the components limit is refused when built"; "independent arithmetic and grouped rounding".

### 8.2 Arithmetic and propagation

**Decided.** One Typed Core runs through a scalar interface. `Rat` implements
rational arithmetic and `Dbl` implements IEEE double arithmetic.
Tensors, charts, closures, data, type inference and the store remain shared.
Definitions do not name an arithmetic backend.

#### 8.2.1 Configuration

| Control | Values | Default |
|---|---|---|
| `:set arithmetic` | `rational`, `double` | `double` |
| `:set propagation` | `montecarlo` | `montecarlo` |
| `:set samples` | 1–100000 input realizations | 10000 |
| `:set roundingAnalysis` | `off`, `stochastic` | `off` |
| `:set roundingSamples` | 2–1000 repetitions per input | 8 |
| `:set seed` | integer | 1 |

The CLI accepts these controls through `--set NAME VALUE`.
Rational arithmetic rejects stochastic rounding analysis.
Changing arithmetic does not change stored term hashes.

#### 8.2.2 Ordinary arithmetic

Ordinary double results use nearest rounding and preserve operation order.
Rational coefficients remain exact under rational operations (§3.2.8).
Sampling does not add an error enclosure to either representation.

#### 8.2.3 Grouped stochastic rounding

For input realization i, evaluate one ordinary result Y_i and R diagnostic
results Z_ij. Each group stores [Y_i, Z_i0, …, Z_i(R−1)].
Without sampled inputs, evaluate one baseline and R diagnostic repetitions.
With analysis off, allocate no diagnostic repetitions.

The random key includes independent input and repetition indices.
Changing R preserves existing indexed repetitions. Changing R or toggling
analysis preserves all ordinary input results.

Basic arithmetic selects adjacent representable neighbors using exact residual
checks, including subnormal cases. Elementary libm functions use a random
one-ulp perturbation heuristic. This is CESTAC-inspired analysis, not a proof
of accuracy or CADNA conformance. Distribution generation and parameter
evaluation are excluded and the report states that exclusion.

#### 8.2.4 Input statistics

Only Y_i contributes to input statistics. Never pool Z_ij into the input sample.
For each input, compute the sample variance s_i² of its diagnostic repetitions.
Report sqrt(mean_i(s_i²)) as typical rounding spread and
sqrt(mean_ij((Z_ij−Y_i)²)) as RMS baseline displacement.
Agreement prints “no variation observed”, not “exact”.

#### 8.2.5 Branches

Ordinary inputs and diagnostic repetitions follow their own branches.
Branch tables report ordinary-input visits and diagnostic visits separately.
They count visits, including repeated visits through recursion.
Reading a shared expression reuses its computed realizations.
Numerical pivoting and matrix exponential scaling run per realization.

#### 8.2.6 Exceptional and mixed outcomes

NaN and infinity remain explicit. Numeric summaries that require finite data
report that they are unavailable when nonfinite values occur.
Domain failures in rational arithmetic fail the evaluation explicitly.
The implementation does not silently discard failed runs or summarize survivors.

Different result constructors produce an ordinary-input outcome table.
Diagnostic constructor counts appear separately. Conditional numeric rounding
summaries for mixed constructors are unavailable.
`mid`, `sd` and covariance reject rounding analysis of reductions.

#### 8.2.7 Batching and resources

**Decided.** Input-only double execution retains bounded parallel batches.
Grouped rounding execution initially uses one bounded grid. Rational execution
is serial. The `cores` setting cannot change results or reports.
The run count must fit both one million and the configured component limit.
Each path receives the total steps budget divided by the number of runs.
This conservative accounting prevents diagnostic work from bypassing the limit.
The memory and time limits cover the entire evaluation.

**Decided.** Keep `async` batch scheduling and the existing demand boundary.
Reading one realization of a deterministic scalar must use its stored value,
without allocating a broadcast vector. Numerical operations and per-realization
matrix kernels use this scalar access path. Formatting grouped samples uses
indexed access or a single forward traversal, never repeated traversal from
the start of a list. These changes preserve operation order, random identities,
batch merging and statistical definitions.

#### 8.2.8 Display and units

Input and rounding summaries retain output units and tensor shapes.
Changing a display unit scales every realization consistently.
A sampled outcome interval describes simulated outcomes, not confidence in the mean.
No report claims a hard numerical bound or significant digits.

#### 8.2.9 Capabilities

Double arithmetic provides `eps`, `nextUp`, `ulps`, `fma`,
`isNaN` and `isInfinite`. Rational arithmetic rejects these format-specific
operations. Both support distributions and input statistics.
Unsupported capabilities fail explicitly rather than switching arithmetic.

**Implemented in:** `Scalar`, `Rational`, `Double`, `Eval`, `Compile`,
`Batch`, `Branch`, `Remark`, `Driver`, `Pretty`, `Numerical.SamplePlan`.
**Tested by:** "independent arithmetic and grouped rounding",
"separate sampling foundation", "limits (design §8.1)", "numerical review regressions".
The allocation regression is "sample arithmetic broadcasts constants without
quadratic allocation"; report alignment is covered by "grouped reports keep
constants and diagnostic offsets aligned".

## 9. Module layout and libraries

The library code is in `lib/`, the executable in `src/` and the tests in `test/`, as [style.md](style.md) requires. [overview.md](overview.md) §5 maps every module to its job and its design section. This section states the rules that the layout keeps.

- **The pipeline's order.** The stages run lexer, parser, desugarer, resolution, inference, lint and evaluation (§1.4). The evaluator (`Metron.Eval`) does not import the session or command modules. `Metron.Compile`, which checks and evaluates one expression for a session, and the session modules (`Metron.Driver`, `Metron.Edit`, `Metron.Source`, `Metron.Session.*`, `Metron.Repl`) sit above the pipeline.
- **The numerical modules stand alone.** `Metron.Numerical.Approx`, `Metron.Numerical.Rational` (over `Metron.Rational`'s magnitudes), `Metron.Rational` and `Metron.Double` import neither the evaluator nor the session types.
- **Hash-level code sits low.** `Metron.Type.Base` and `Metron.Encode` sit below `Metron.Builtin`, which needs the hashes of the built-in declarations, and below `Metron.Type` and `Metron.Hash`.
- **The executable is thin.** `src/Main.hs` parses the command line (§7.4), opens the store and runs `Metron.Driver.feed` under the limits (§8.1). It sets the starting `cores` to the machine's logical core count. Everything the tests reach is in the library, including the REPL's completion, colour and continuation rules (`Metron.Repl`).
- **One C file.** `cbits/limits.c` sets the runtime's maximum heap while the program runs, for the `memory` limit (§8.1).
- **Runtime options.** The executable is built with `-threaded` and runs the young generation's collections on one thread and the older generations' on four (`-with-rtsopts=-qg1 -qn4`). With every core collecting in parallel, the number of collection threads affects performance. The test suite runs with `-T`, so that it can measure its own memory (§8.1).

**Libraries.** The library depends on `async`, `base`, `bytestring`, `containers`, `cryptohash-sha256`, `directory`, `filepath`, `megaparsec`, `mtl`, `parser-combinators`, `text`, `time`, `transformers`, `unicode-transforms` and `vector`. The executable adds `haskeline` and `process`. The tests use `tasty`, `tasty-hunit`, `tasty-quickcheck` and `QuickCheck`.

**Property tests.** These hold over randomly generated programs, from two generators: a blind one, which ignores types and so reaches shapes no typing rule suggests, and a type-directed one, which builds each program from a chosen closed type (doc/core.md §9):

- Whatever inference accepts, lint accepts with the same type.
- The type a program was built for is an instance of the type inferred for it.
- Printed Core, in ASCII and in unicode, re-parses to an alpha-equivalent term.
- Hashes ignore hints, and the hash is stable across printing.
- The storage encoding round-trips every program, hints included.
- Inference is deterministic.
- Evaluating a linted term never reports an internal error.

Regression seeds are replayed by name. Independent tests check rational approximation kernels, IEEE residuals, dimensions, source identity and separate sample summaries.

**Performance.** Input and diagnostic costs depend on run counts and arithmetic. The removal plan records measurements for the current implementation.

**Implemented in:** `src/Main.hs`; `cbits/limits.c`; `metron.cabal`.
**Tested by:** "properties" › "blind programs", "typed programs", "replayed seeds"; "rational approximation kernels"; "dimension syntax"; "independent arithmetic and grouped rounding".

## 10. Roadmap

This is the one list of pending work. Everything built is described in its own section and is not repeated here. An item is **Designed** when its design is decided and only the building is left, and **Open** when the design is not settled. Questions that need the owner's decision are in §11. Each item names the section that has its context.

### 10.1 Numbers and error

- **Open.** Chunk grouped rounding grids while preserving indexed randomness,
  branch reports and reduction order.
- **Open.** Specify diagnostic accessors and rounding analysis of reductions.
- **Open.** Add hierarchical distributions and explicit resampling semantics.
- **Open.** Improve matrix kernels with Padé approximants and sparse rotation chains.
- **Open.** Add conditional numeric summaries for mixed constructors.

### 10.2 Types and Core

- **Dictionary passing** (Designed, §4.2, §5.3). An unresolved product constraint is defaulted at generalisation. With dictionaries it becomes a parameter of the definition, so `\k v -> 2 * k * v` is polymorphic in the rank of `k`. A dictionary is a record of data constructors, so this needs no new Core form (doc/core.md §8).
- **Run-time errors with a location** (Open, §4.7). A failing primitive application reports no span, and an error at a use of a stored reference does not name the definition and its stored type.
- **Provenance paths** (Open, §4.7). The paths of the provenance table and those inference walks disagree inside `case` alternatives, `if` branches and list literals, so a type error deep inside one of them gets the definition's span or another node's. Fixing it moves the error excerpts of existing inputs, so it is a change of its own.
- **Polymorphic recursion** (Open, §4.6). A signature is checked after inference, so a recursive use sees the member's one monomorphic type.
- **Mutually recursive data types** (Open, §2.3). A declared type can refer to itself, not to another type of the same group.
- **`cbrt`** (Open, §4.6). `^` needs a literal exponent and `sqrt` covers the half power. A cube root is the next such function.
- **Mixed-dimension matrices in the type system** (Designed, §3.7.1). Hart's route is written down rule by rule, with what building it takes. It starts only on the escalation signal of §3.7.2: block formulas beyond 2 × 2 blocks, or the inverse of a single matrix of mixed dimensions.
- **Constraints over `Diff`** (Open, §3.10, F4). Only the pending `Diff c ~ Tensor σ δ` exists. A definition that leaves it pending must name its space in a signature.
- **Printing values with `·`** (Open, §4.1). A value's units print juxtaposed (`9.81 m s^-2`). A unicode spelling with `·` is not decided.
- **A compiler** (Open, §8). Long propagations wait for a compiler from Typed Core, which reads the explicit dimension and length arguments for static shapes.
- **Rewrite rules for products** (Open, §3.3). Fuse `star (wedge a b)` back into a hand-written 3D cross product, and notice when only part of a product is consumed. Laziness avoids the arithmetic of the unread part, not its allocation.

### 10.3 Charts, frames and axes

- **Named positions, `axes x y z`** (Designed, §3.9 layer 1, §2.10). Labels for positions 0, 1, 2 in a namespace, so that `v.x` desugars to `v.0` with the same hash.
- **`fromQuaternion`** (Designed, §3.8). The logarithm of a rotor, for input only.
- **A declared spin is not checked** (Open, §3.8). Nothing checks that a chart's `spinning` clause is the derivative of its rotation. A finite difference checks it by hand.
- **An origin that moves relative to its parent** (Open, §3.8). `v_o_abs` counts only the parent's spin. A chart whose origin is a function of its time parameter needs a declared origin velocity.
- **Known gaps of axis sets** (Open, §3.9). The store's log keeps a re-stamped chart's new version, not the step between, after `:rename`. A chart redefined as no chart drops its axes' type label in the session, and the log does not record it. A root chart's origin from a named value needs a signature such as `o :: forall (a : 3). Vec a m`. `withAxes`'s printed type does not show that its argument is anonymous. `det`'s `Mat n a` reads back with a length of its own. In a group where a chart uses the group's own data constructors, a signature or data field that names the chart's axes is refused.
- **A `data` declaration that names a chart's axes** (Open, §3.10, Part F). Pending in one group with that chart, it is read before the chart. `:add` the chart first.

### 10.4 Library and codebase

- **The second `astro` build** (Designed, §7.7). Time: TAI and GPS charts, leap seconds, GMST and the Earth rotation angle, and the function from TT to UTC over a leap-second table. Frames: `GCRS`, a moving `ecef`, ENU and SEZ, perifocal, LVLH and RSW. Geodesy: WGS84 geodetic coordinates, azimuth, elevation and range. Then Lambert. UT1 and TAI are not modelled until then. The Earth chart is the owner's decision (§11).
- **The atomic mass unit `u`** (Open, §7.7). Not shipped.
- **A `brick` front end** (Designed, §7.3). `metron --tui` beside the line REPL: the unicode echo live as you type, completion as a popup, multi-line editing, and room for panes (a `:ls` sidebar, the error excerpt beside the input). It is built on the same `Metron.Repl` logic, so the two never drift. The line REPL stays the default and the only front end for piped scripts and tests. `brick` and `vty` come in through `build-depends`.
- **Recreating the owner's store** (Open, §7.4). A store of an older format is refused, not migrated. The owner's store is to be recreated at format 13 from explicitly rewritten source, and the export checked to read back to the same labels.

## 11. Open questions

These need the owner's decision. Each names the section with its context.

### 11.1 Numbers and error

- **Open.** Choose an API for new input distributions and their parameter validation.
- **Open.** Decide whether `floor`, `ceil` and `round` should accept dimensioned quantities.
- **Open.** Specify a representation for failed individual runs before adding survivor statistics.
- **Open.** Decide whether a future precision-refinement interface is useful beyond explicit rational precision.

### 11.2 Types

- **A shape whose lengths are all one `n`** (§4.3). `transformBy` checks at run time that every length of its tensor is the matrix's `n`, because the shape language cannot say it. A shape language with "every length is `n`" makes it a type error. The plan is to wait for a second primitive that needs it.
- **The type of a definition that uses a signed name** (§4.8). `let h y = f y` with `f :: Num m -> Num m` keeps its Core's type, `a -> a`, so `h (3 s)` works where `f (3 s)` is refused. Stored types are a function of the hash, which cannot see labels. Give such a definition the narrower type it was checked at as a signature of its own, or refuse a use through it another way? An ascription inside a definition has the same limit. Propagation re-checks a moved dependent only against its own signature.
- **Equality on declared types** (§4.2). Equality is derived structurally when every field has it. May a type opt out, or give its own equality (a fraction kept as an unreduced pair, which structural equality calls unequal to its reduced form)?

### 11.3 Charts and frames

- **A frame per item of data** (§3.10, F3). Frames are minted by declarations, so their number is fixed when the code is written, which the owner accepts for now. Bodies that come from data, a list of a hundred satellites, cannot each be declared, and one parameterised chart makes them one frame. The candidates:
  - A scoped frame in the style of `runST` (`frame c = chart in body`, a rigid frame that cannot escape its scope, so points leave it only converted).
  - Existential packages of a chart and its points (`data Body = forall c. Body (Chart c) {Point c}`), the general form, which needs existential types and the same escape check.
  - A run-time identity check, which gives up the guarantee of the checker.
- **Curvilinear charts** (§3.8). A chart is affine, so latitude and longitude, spherical coordinates and topocentric azimuth, elevation and range are functions (`toGeodetic : Point ecef -> Geodetic`), not charts. A curvilinear chart can be defined by a pair of functions to and from an affine parent, `chart geodetic on ecef via toGeodetic fromGeodetic`: its points typed by frame, `to` converting through the functions, and `.-` and `.+` refused, since a difference of coordinates on a curved chart is not an amount ("subtract on an affine frame: `b .- a on ecef`"). A lighter form is a `coordinates polar = to toPolar from fromPolar` declaration that bundles the pair, so that `v to polar` reads like `p to eci`. Its inverse cannot be checked, and its `to` must stay distinguishable from the exact, affine `to` on a chart. Wait for a use, which iapetus can bring.
- **An Earth chart** (§3.8). None is shipped. An Earth-fixed chart honest at the kilometre level needs precession and nutation (the equinox of date has moved about 0.36° from J2000's by 2026, some 40 km at the equator), polar motion, and UT1 rather than UTC. §12.5 defines a simple one for illustration, with its accuracy stated.
- **`GCRS` and `eci` in the library** (§3.8). None is shipped. A user's `space GCRS = Vec 3 m` and `chart eci on GCRS` are a space and a root like any other.
- **`astro.State` and points** (§3.8, F10). `State` holds its position as an amount from the space's base origin. Should it hold a point on a frame instead? With today's `State`, F10's `lvlh` origin is written `(s.pos - originOf (ecef s.epoch)) to (ecef s.epoch)`.
- **`fromState`'s cases by tolerance** (§7.7). Numerical residuals can classify a circular orbit as slightly eccentric. Should an explicit user-selected tolerance decide these cases?

### 11.4 Codebase and REPL

- **Upgrading a codebase** (§7.7). How a codebase takes newer versions from a newer library or from another codebase. `:stdlib upgrade` is a sketch: it reads "never touched" off a name's history, so a name moved by an earlier upgrade counts as the user's. `--merge` is the wrong tool, because its last-writer rule overrides the user's edits.
- **The iapetus store** (§7.4). `:export` writes the codebase as source that reads back to the same labels and hashes, so both the store and the export can be committed. Can the store then be dropped, which loses history?
- **`:ls` and fields across namespaces** (§7.6). Should `:ls` show more of the tree than one level? Should a field be reachable by path from outside its namespace?
- **A root name that shadows the library** (§7.7). A root constructor named like a library unit (`data Temp = T …`) shadows the tesla `si.T` silently, as any root name shadows the library's. Warn?
- **`h` for the hour** (§7.7). `h` is also the hecto prefix in compound names like `hPa`. The prefix only appears attached to a unit, so there is no lexical clash, but readers can stumble.
- **The style of a stale reference** (§7.2). `:view` prints a reference whose name has moved on as `x#a3f9k`, Unison's style. Or `#a3f9k` alone?
- **What `:edit` leaves** (§7.3):
  - `:update` of a `data` type does not move the definitions that build or match its constructors, and `:edit` does (`Metron.Update.propagateWith`). Should `:update` do the same?
  - A type outside the edited file whose fields use an edited type keeps the old one, and the report says so. `:rename` re-declares such a type (§7.2). Follow it here too, or ask for a wider scope?
  - A definition deleted from the file that another definition in the file still uses resolves to the codebase's version while the file is entered, so the user is left stale (and told). Refuse that edit instead?
  - What does not round-trip through `:export` (§7.4) does not round-trip through `:edit`: two labels on one stamped or recursive reference, and a stamp that no longer matches its path, report as updated from an unchanged file.

## 12. Worked scenario: iapetus

These sessions show the pieces working together on the owner's orbital-mechanics use. The first two are copied from a run of `metron --no-codebase -i` and print what is shown, except the hashes, which depend on the build's standard library. The last three are the test suite's own sessions: each test checks every output shown, so they stay true.

### 12.1 Constants, functions and sampling

```text
:set samples 1000
use astro
use astro.kepler
use astro.iers2010
let radius = 7000 km
period earth radius to min
sd (period earth radius) to s
```

The input statistics describe the declared distributions of physical constants.
They do not include a guaranteed floating-point or solver error bound.

### 12.2 A new published constant

Definitions retain their content-addressed dependencies. Update a chosen body's
declaration, accept it with `:update`, and inspect affected definitions with
`:todo`. Historical references still identify their original dependencies.
A changed sample owner also changes its source identity.

### 12.3 A filter step in blocks

```text
use linalg
let x = sample (normal (7000 km) (1 km))
let y = sample (normal (0 km) (1 km))
let z = sample (normal (0 km) (1 km))
let vx = sample (normal (0 km/s) (1 m/s))
let vy = sample (normal (7.5 km/s) (1 m/s))
let vz = sample (normal (0 km/s) (1 m/s))
let r0 = [x, y, z]
let v0 = [vx, vy, vz]
let r1 = r0 + 10 s * v0
jointCovariance (r1, v0)
```

The blocks are empirical covariances of paired samples.
Independent latent inputs can have nonzero empirical cross-covariance.

### 12.4 A perifocal chart

```text
space Flight = Vec 3 m
chart eci on Flight
chart pf on eci step km by rotz (30 deg) then rotx (45 deg) then rotz (60 deg)
[7000, 0, 0] pf to eci
```

The point carries its frame. Explicit conversion rotates and translates coordinates.
Round trips can leave small numerical residuals.

### 12.5 A spinning Earth

```text
space Flight = Vec 3 m
chart eci on Flight
chart earth t on eci by rotz (7.292115e-5 rad/s * t) spinning [0, 0, 7.292115e-5] rad/s
[6378137, 0, 0] (earth (100 s)) to eci
```

A moving chart's spin contributes to velocity transformations.
Input distributions can describe uncertain angles or spin rates.
The runtime evaluates the complete transformation for each realization.

**Implemented in:** `Prelude`, `Eval`, `Rational`, `Double`, `Update`.
**Tested by:** "astro (design §7.7)", "movingCharts", "rotations".

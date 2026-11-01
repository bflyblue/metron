# Learning Metron

Metron is a calculator and small language for physical calculations. It keeps units attached to numbers and follows uncertainty through formulas. It also stores reusable definitions with a history of their changes.

This tutorial starts with a cycling calculation. It then introduces measurement uncertainty, vectors, coordinate systems, and structured data. The final sections explain the saved database and demonstrate how a function update affects other definitions.

Metron is a proof of concept. The examples below describe working features, but the language and storage format can change. Old databases have no migration guarantee.

## 1. Open a practice session

With [Nix](https://nixos.org/download/) installed, run this shell command from the project directory:

```sh
nix run . -- --no-codebase
```

This opens the interactive calculator without a saved database. Enter the examples at its prompt. Do not type the prompt itself.

Blocks marked `text` contain Metron input unless they are introduced as output. Blocks marked `sh` contain shell commands. Definitions normally produce no output, while expressions print their results.

Continue in the same session through sections 2–7. Section 8 starts a separate session with a saved database.

Useful commands include:

- `:help` lists the available commands.
- `:type expression` shows the type of an expression.
- `:quit` leaves the calculator.

For a single calculation without an interactive session, run:

```sh
nix run . -- --no-codebase '5 km to m'
```

The result is `5000 m`. If you already have the `metron` executable available, use it in place of `nix run . --`.

## 2. Calculate a ride time

Suppose you cycle 12 kilometers in 30 minutes. Give each measurement a name:

```text
let distance = 12 km
let duration = 30 min
let speed = distance / duration
speed to km/h
```

The result is:

```text
24 km h^-1
```

`h^-1` means “per hour.” Metron divides both the values and their units. The `to` expression chooses the units used to display the result.

Try another display unit:

```text
speed to m/s
```

The result starts with `6.6666666666666666666… m s^-1`. Metron retains the exact fraction internally. The ellipsis means that the decimal display continues beyond the printed digits.

### Make the formula reusable

A function takes inputs and calculates a result. Define one that takes both distance and speed:

```text
let travelTime distance speed = distance / speed
travelTime (18 km) speed to min
travelTime (18 km) (15 km/h) to min
```

The two calls give `45 min` and `72 min`. The parameter named `speed` belongs to the function. Each call supplies its value explicitly.

Parentheses keep a quantity together when you pass it to a function. Write `travelTime (18 km) speed`, rather than `travelTime 18 km speed`.

You can reuse the same approach for energy:

```text
let kineticEnergy mass speed = mass * speed^2 / 2
kineticEnergy (80 kg) (18 km/h) to J
```

This gives `1000 J`. The calculation includes the conversion from kilometers per hour to meters per second.

### Let the units catch mistakes

A dimension describes a physical kind, such as length or time. Different units can describe the same dimension. Meters and kilometers are both lengths.

Try this deliberate mistake:

```text
1 m + 1 s
```

Metron refuses it because length and time cannot be added. Multiplication and division can combine dimensions, as they do in the speed and energy formulas.

Use `:type` to inspect the information Metron infers:

```text
:type speed
:type travelTime
```

A function can have a more general type than its example calls suggest. Metron infers relationships between input and output dimensions instead of assuming every argument is a plain number.

### Define a useful unit

Suppose one lap of your track is 400 meters:

```text
unit lap = 400 m
5 lap to km
```

The result is `2 km`. A unit definition makes `lap` available as a quantity suffix and as a conversion target. Ordinary values use `let` instead.

For a calculated number, attach a unit with multiplication, as in `(2 + 3) * km`. When passing a unit-sized amount to a function, write `1 km`. A bare unit is not a general value that you can pass around by itself.

## 3. Follow measurement uncertainty

A measurement bound gives a range that contains the value. Here, a board has a measured length of 2 meters with a bound of 0.01 meters:

```text
let boardLength = (2 ± 0.01) * m
let boardWidth = (1 ± 0.005) * m
let perimeter = 2 * (boardLength + boardWidth)
perimeter
```

The result is:

```text
6.00 ± 0.03 m
```

The `±` operator declares a bound. You can type `+-` instead. Parentheses group the uncertain number before multiplication attaches the unit.

### See where the bound comes from

An error budget lists the contributions to an uncertain result. Ask Metron for the perimeter's budget:

```text
:budget perimeter
```

The length contributes `0.02 m`, and the width contributes `0.01 m`. Metron reports these as approximately 67% and 33% of the total bound. This helps you decide which measurement needs improvement.

Repeated use of one uncertain value retains its shared error:

```text
boardLength - boardLength
```

The result is exactly `0 m`. Both occurrences refer to the same measurement, so their errors cancel. This differs from subtracting two independent measurements with similar printed ranges.

### Distinguish a bound from statistical uncertainty

Statistical uncertainty describes spread rather than a guaranteed range. Metron uses `±σ` for standard uncertainty, with `+-s` as its ASCII spelling. Do not interpret one standard uncertainty as a hard limit.

```text
let reading = (10 ±σ 0.2) * m
let doubled = 2 * reading
doubled
sd doubled
```

The results are `20.0 ±σ 0.4 m` and `0.4 m`. The function `sd` extracts the standard uncertainty. Doubling a reading doubles its standard uncertainty too.

Covariance measures how two uncertain values vary together. Inspect the original reading and its doubled value:

```text
:covariance [reading, doubled]
```

Metron prints:

```text
covariance [0.04, 0.08; 0.08, 0.16] m^2
bound box [0, 0] m
```

The nonzero off-diagonal entries show that these values share uncertainty. They are not independent measurements.

Statistical propagation uses a first-order approximation. Nonlinear calculations can exceed that approximation's limits, and Metron can mark results or refuse uncertainty summaries. Its error tracking does not replace a measurement model or establish that your declared bounds are correct.

## 4. Work with vectors and matrices

A vector is an ordered set of components. Use square brackets to write one. The following velocity has components of 3, 4, and 0 meters per second:

```text
let velocity = [3, 4, 0] m/s
let elapsed = 10 s
let displacement = velocity * elapsed
displacement
```

The result is `[30, 40, 0] m`. Multiplying by time changes velocity into displacement. Each component carries the same physical dimension.

### Choose the right product

Metron supports several products, with different meanings for tensors. A matrix is a rectangular array of components. The table also includes division and the related `star` operation:

| Operation | Unicode | ASCII | Function | Meaning |
| --- | --- | --- | --- | --- |
| Tensor (outer) product | `a ⊗ b` | `a * b` | `outer a b` | Multiplies every component of `a` by every component of `b`. Two vectors produce a matrix. A scalar scales the other operand. |
| Contracting product | `a · b` or `a ⋅ b` | `a @ b` | `dot a b` | Multiplies and sums over the last axis of `a` and the first axis of `b`. Includes vector dot products and matrix multiplication. |
| Elementwise product | `a ⊙ b` | `a .* b` | `emul a b` | Multiplies corresponding components. Both tensors must have the same shape. |
| Wedge (exterior) product | `a ∧ b` | `a /\ b` | `wedge a b` | Represents the oriented plane of two equal-length vectors, stored as an antisymmetric matrix. |
| Cross product | `a × b` | `a >< b` | `cross a b` | Produces a perpendicular vector from two three-component vectors, using the right-hand rule. |
| Elementwise division | `a ⊘ b` | `a ./ b` | `ediv a b` | Divides corresponding components. Both tensors must have the same shape. |
| Scalar division | `a ÷ s` | `a / s` | `div a s` | Divides every component of `a` by the scalar `s`. |
| 3D Hodge star | `⋆ b` | `star b` | `star b` | Converts an oriented-plane matrix in three dimensions to its normal vector. This is a unary operation, not a product. |

The two spellings in each row perform the same operation. For matrix multiplication, use `·` or `@`. The `*` operator always means the tensor product, including scalar scaling.

Products multiply the operands' physical units. Division divides their units, while `star` preserves its input's units. Shapes and coordinate axes must also be compatible with the chosen operation.

Compare three products of the same vectors:

```text
let a = [1, 2]
let b = [3, 4]
a ⊗ b
a · b
a ⊙ b
```

The results are a matrix `[3, 4; 6, 8]`, a number `11`, and a vector `[3, 8]`, respectively. In ASCII, the same expressions are `a * b`, `a @ b`, and `a .* b`.

The wedge product stores the matrix `a ⊗ b - b ⊗ a`. An antisymmetric matrix changes sign when its rows and columns are exchanged. In three dimensions, applying `star` to this matrix gives the cross product:

```text
let u = [1, 0, 0]
let v = [0, 1, 0]
u ∧ v
u × v
⋆ (u ∧ v)
```

The wedge result is `[0, 1, 0; -1, 0, 0; 0, 0, 0]`. Both remaining expressions give `[0, 0, 1]`. In ASCII, write `u /\ v`, `u >< v`, and `star (u /\ v)`.

The wedge product works with equal-length vectors beyond three dimensions. The cross product and this `star` operation are specific to three dimensions. Here, `∧` means wedge, while boolean “and” uses `&&`.

### Calculate speed and work

A dot product multiplies matching components and adds the results. Metron writes it as `·`. The dot product of a vector with itself gives its squared magnitude:

```text
sqrt (velocity · velocity) to m/s
```

The result is `5 m s^-1`. The units follow the square and square root operations.

Work is the dot product of force and displacement:

```text
let force = [10, 0, 0] N
force · displacement to J
```

The result is `300 J`. Only the displacement component in the force's direction contributes.

### Apply a matrix

Semicolons separate a matrix's rows. The `@` operator performs matrix multiplication:

```text
let swap = [0, 1, 0; 1, 0, 0; 0, 0, 1]
swap @ displacement
```

This gives `[40, 30, 0] m`, with the first two components exchanged. This matrix is dimensionless, so the result retains the displacement's units.

You can also solve a small linear system using an inverse:

```text
let a = [2, 0; 0, 4]
inverse a @ [6, 8]
```

Because `a` was defined earlier in the session, the new definition first prints ``replaced pending definition of `a` ``. The result is `[3, 2]`. This solves `a @ x = [6, 8]` for `x`. An inverse requires a suitable square matrix and can fail for a singular matrix.

Tensors extend vectors and matrices to more axes. Metron tracks their shapes and dimensions. Shape mistakes, such as incompatible matrix sizes, are errors rather than implicit resizing.

## 5. Separate points from changes

A point describes a position relative to an origin. A change describes a difference between points. This distinction matters for temperature scales and coordinate frames.

### Start with temperature

Celsius and Fahrenheit have different zero points. Convert a temperature point with `to`:

```text
20 degC to degF
```

The result is `68 degF`. Find a temperature change with `.-`, or add a change to a point with `.+`:

```text
25 degC .- 20 degC
20 degC .+ (5 K)
```

These give `5 K` and `25 degC`. A temperature point and a temperature change have different roles. Adding two Celsius points with ordinary `+` is rejected.

### Place objects in a workshop

A space identifies the physical setting that points belong to. A chart supplies coordinates within that space. Define a three-dimensional workshop measured in meters:

```text
space Workshop = Vec 3 m
chart room on Workshop
chart bench on room at [2, 1, 0] m
```

The bench's origin is 2 meters along the room's first axis and 1 meter along its second axis. Its axes currently point in the same directions as the room's axes.

Place a tool one meter along the bench's first axis:

```text
let tool = [1, 0, 0] bench
tool to room
```

The result is `[3, 1, 0] room`. The conversion includes the bench's origin offset.

Find a displacement in bench coordinates and use it to move a point:

```text
let shift = [2, 0, 0] bench .- [1, 0, 0] bench
shift
([1, 0, 0] bench .+ shift) to room
```

The displacement prints as `[1, 0, 0] m`. The moved point becomes `[4, 1, 0] room`. A displacement does not include the chart's origin offset.

### Rotate the axes

A rotated chart changes the directions of its axes. Define a chart turned 90 degrees around the third axis:

```text
chart turned on room by rotz (90 deg)
[1, 0, 0] turned to room
```

The result is approximately `[0, 1, 0] room`. Rotation calculations can print tiny error bounds near zero and an ellipsis near one. Those values reflect numerical approximation, not an extra physical displacement.

Now convert a displacement between the same axes:

```text
let turnDelta = [1, 0, 0] turned .- [0, 0, 0] turned
:type turnDelta
turnDelta from turned to room
```

The type of `turnDelta` is `Vec turned m`. The converted result is approximately `[0, 1, 0] m`, and its type is `Vec Workshop m`: it now lies along the target's axes, although both display only meters.

Use `point to chart` for point conversion. Use `delta from source to target` when explicitly converting a displacement between charts. Convert differently oriented displacements to matching axes before adding them.

Do not assume that matching printed units imply matching coordinate systems. Two vectors can both print in meters while referring to different axes or different spaces.

## 6. Process several rides

A list is a sequence of values. Lists use braces, while tensors use square brackets. Use `map` to apply a function to each list element:

```text
let times = map (\d -> travelTime d (18 km/h)) {3 km, 6 km, 9 km}
times
```

The results are one-sixth, one-third, and one-half of an hour. Metron prints the first two as repeating decimals. The expression `\d -> ...` is a function written without giving it a name.

Use `foldl` to combine the results from left to right:

```text
foldl (\total time -> total + time) (0 s) times to min
```

This gives `60 min`. The initial total is `0 s`, with a time unit. Each step adds one time to that total.

## 7. Give your data and formulas structure

A record groups named fields into one value. Define a ride with a distance and a duration:

```text
data Ride = Ride {distance :: Num m, duration :: Num s}
let morning = Ride {distance = 12 km, duration = 30 min}
let averageSpeed ride = ride.distance / ride.duration
averageSpeed morning to km/h
```

The result is `24 km h^-1`. The field types require length and time, but they do not require a particular display unit. A distance in kilometers fits `Num m` because both describe length.

### Choose between named cases

A data type can also describe a choice. Here, a pace is either `Brisk` or `Steady`:

```text
data Pace = Brisk | Steady
let paceLabel ride = if averageSpeed ride > 20 km/h then Brisk else Steady
paceLabel morning
```

The result is `Brisk`. The `if` expression chooses a value based on a condition. A comparison involving uncertainty can be undecidable if its possible values cross the boundary.

Use `case` to calculate a result for each named choice:

```text
let restMinutes pace = case pace of Brisk -> 10 min; Steady -> 5 min
restMinutes (paceLabel morning)
```

This gives `10 min`. Both branches return a time. The compiler checks that the alternatives agree on their result type.

### Organize names

A namespace groups related definitions under a shared prefix. Enter this block, then enter a blank line to finish it:

```text
namespace cycling
  let travelTime distance speed = distance / speed
```

You can call the function by its full name:

```text
cycling.travelTime (18 km) (24 km/h) to min
```

The result is `45 min`. Commands such as `:ls cycling` and `:view cycling.travelTime` help you inspect the group.

You can use `:use cycling` to make its names available without the prefix; Metron confirms with `stored use cycling`. Existing local names can affect lookup, so full names remain useful when names overlap.

## 8. Start a saved database

Quit the practice session with `:quit`. From the project directory, start a separate store at a new path:

```sh
nix run . -- --codebase /tmp/metron-learning-store
```

If that directory already contains earlier work, choose a different path. This tutorial uses `/tmp` for practice, so the operating system can remove it later. Use a durable directory for work you want to keep.

The database is also called a codebase. It stores definitions and the names that refer to them. It is a directory of files rather than a separate database server.

Create some definitions:

```text
let five = 5
let alsoFive = 5
let addOne x = x + 1
let increment y = y + 1
:scratch
```

The scratch is a temporary workspace for pending definitions. You can already use these definitions in calculations, but they are not yet saved. Accept them with:

```text
:add
```

`:add` saves new definitions. If a saved name already has a different definition, Metron asks you to use `:update`. This separates experimenting with a definition from accepting its replacement.

## 9. Understand content-based identity

A hash is an identifier calculated from a definition's content. Metron uses hashes to identify definitions and their dependencies. Names are labels that point to those identities.

### Two names can identify one definition

Compare the two values:

```text
:hash five
:hash alsoFive
```

Both commands print the same hash. Compare the functions too:

```text
:hash addOne
:hash increment
```

These also share a hash. Renaming a function parameter from `x` to `y` does not change its meaning or its identity. The parameter names help people read the source, but do not distinguish these definitions.

You can add another label explicitly:

```text
:alias fiveAgain five
fiveAgain
```

The result is `5`. The alias gives an existing definition another name. It does not copy or recalculate its body.

To inspect its names, run `:hash five`, then pass the printed identifier to `:names`. For example, if the output is `#ico3k`, enter `:names #ico3k`. Use the hash from your own session.

### Equal results do not guarantee equal hashes

Define another expression that evaluates to five:

```text
let computedFive = 2 + 3
computedFive
:hash computedFive
:hash five
```

The result is still `5`, but these definitions have different hashes. Metron identifies stored expressions, not every mathematical equivalence between them. It does not prove that two arbitrary programs always produce the same result.

Save the new definition before continuing:

```text
:add
```

A hash also includes the identities of referenced definitions. Changing a dependency creates a new identity for an upgraded dependent, even when its displayed source still uses the same names.

## 10. Upgrade a function deliberately

Create a travel-time function and a saved calculation that uses it:

```text
let journeyTime distance speed = distance / speed
let commute = journeyTime (12 km) (24 km/h)
:add
commute to min
```

The result is `30 min`. The saved `commute` refers to this specific version of `journeyTime`. It does not look up whichever definition happens to have that name each time it runs.

Inspect the relationship:

```text
:hash journeyTime
:hash commute
:dependents journeyTime
```

The final command lists `commute`. A dependent is a definition that refers to another definition. Note the two hashes so you can compare them after an upgrade.

### Change the function without upgrading its dependents

Suppose the estimate needs five minutes of preparation time. Propose a new function and accept it without changing its dependents:

```text
let journeyTime distance speed = distance / speed + 5 min
:scratch
:update --no-upgrade
```

Metron moves the name `journeyTime` to the new definition. It reports that `commute` remains on an old version. The old definition still exists in the store.

Compare direct use of the new function with the saved calculation:

```text
journeyTime (12 km) (24 km/h) to min
commute to min
```

The results are `35 min` and `30 min`. This difference is intentional. Updating a label without upgrading dependents preserves the saved calculation's original dependency.

Inspect the old reference and the history:

```text
:view commute
:todo
:history journeyTime
```

The view contains a reference resembling `journeyTime#ma5cf`. The suffix identifies the older version. The history lists the current version first, followed by earlier versions.

You can call that older function directly. Replace `ma5cf` below with the old hash from your own history if it differs:

```text
journeyTime#ma5cf (12 km) (24 km/h) to min
```

The result is `30 min`, even though a call to the current `journeyTime` gives `35 min`. Keep the name and `#` together. A named hash searches versions previously or currently associated with that name.

A bare hash searches the stored definitions without requiring a name:

```text
#ma5cf (12 km) (24 km/h) to min
```

This also gives `30 min`. A prefix must identify one definition, or Metron reports the ambiguity and shows the full matching hashes. A bare hash that refers to a recursive function group needs a member suffix, such as `#dlcnc.0`, because the hash names the whole group; `:hash` prints it with the suffix. A named reference such as `fact#dlcnc` needs no suffix.

When passing a bare hash as a function argument, put it in parentheses, as in `f (#hash)`. This distinguishes the reference from a trailing measurement label such as `5 ± 1 #sensor`. A glued `name#hash` is always a version reference, so separate measurement labels from preceding names with whitespace.

These expressions select the old content when they are resolved. A saved definition made with them still participates in the normal upgrade rules. Selecting a version does not create a permanent exemption from `:upgrade` or `:update`.

The todo command identifies `commute` as stale and suggests an upgrade. Here, “stale” means that a newer dependency version is available. It does not mean that the original calculation is invalid.

### Upgrade the saved calculation

Move the dependent calculation to the new function:

```text
:upgrade journeyTime
commute to min
:hash commute
:todo
```

The result is now `35 min`. The hash of `commute` changes because its dependency changes. The todo command now reports `nothing to do`.

The upgrade creates a new dependent definition. It does not overwrite the old content under the old hash. The name `commute` moves to the upgraded definition.

### Use the default automatic upgrade

Now increase preparation time to ten minutes:

```text
let journeyTime distance speed = distance / speed + 10 min
:update
commute to min
:history commute
```

The result is `40 min`. Plain `:update` also attempts to upgrade dependents, so no separate `:upgrade` command is needed in this example. The history retains the earlier identities of `commute`.

Changes that make dependent definitions ill-typed can leave unresolved work. Use `:todo` after an update to inspect what remains. Successful propagation in this example does not mean every possible replacement is compatible.

## 11. Reopen and inspect the store

Quit the session, then run this shell command with the same directory:

```sh
nix run . -- --codebase /tmp/metron-learning-store 'commute to min'
```

The result is still `40 min`. Metron reloads the accepted definitions and their names. Pending scratch definitions do not survive a restart unless you accept them first.

The directory contains several kinds of files:

| Entry | Purpose |
| --- | --- |
| `format` | Identifies the store format that Metron can open. |
| `terms/` | Stores expressions and functions under their content hashes. |
| `types/` | Stores declared types under their content hashes. |
| `names.log` | Records changes to names and other saved metadata. |
| `history` | Holds interactive input history, separate from definition history. |

Use Metron's commands to change the database. The content hashes identify stored definitions, while the name log records which definitions names refer to. This separation allows names to change without rewriting old definitions.

Without `--codebase`, Metron searches upward for a project-local `.metron/` directory. If it finds none, it uses the user data directory, normally `$XDG_DATA_HOME/metron` or the platform default. The `:store` command shows the active store path.

### Export readable source

Open the saved session again and export its current definitions:

```sh
nix run . -- --codebase /tmp/metron-learning-store
```

Then enter:

```text
:export /tmp/metron-learning.metron
```

The file contains source that you can read or load. Export represents the current definitions, not the entire database history. It also excludes unaccepted scratch work.

To try the exported source in a separate in-memory session:

```sh
nix run . -- --no-codebase
```

Enter:

```text
:load /tmp/metron-learning.metron
commute to min
```

The result is `40 min`. Loading source gives you definitions to work with. In a saved session, use `:add` or `:update` to accept them as appropriate.

For the full language reference, read [the design document](doc/design.md). For the implementation model, read [the core overview](doc/core.md). The [README](README.md) provides a shorter introduction.

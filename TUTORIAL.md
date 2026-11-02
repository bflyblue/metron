# Learning Metron

Metron is a calculator and small language for physical calculations. It checks units, samples uncertain inputs, and stores reusable definitions with a history of their changes.

This tutorial starts with a cycling calculation. It then introduces measurement uncertainty, vectors, coordinate systems, and structured data. The final sections explain the saved database and demonstrate how a function update affects other definitions.

Metron is a proof of concept. The examples below describe working features, but the language and storage format can change. Old databases have no migration guarantee.

## 1. Open a practice session

With [Nix](https://nixos.org/download/) installed, run this shell command from the project directory:

```sh
nix run . -- --no-codebase
```

This opens the interactive calculator without a saved database. Enter the examples at its prompt. Do not type the prompt itself.

Blocks marked `text` contain Metron input. Comments beginning with `-- =>` show the important results, so you can copy whole blocks. Results marked “about” or “rounded” summarize longer output. Sample statistics vary with the seed and sample count. Blocks marked `sh` contain shell commands.

Definitions normally produce no output, while expressions print their results. Continue in order: later examples reuse earlier definitions.

Metron starts with double arithmetic, which uses fixed-precision floating-point numbers. These examples begin with rational arithmetic to keep fractions exact. Select it first:

```text
:set arithmetic rational
```

Elementary functions, such as `sqrt` and `sin`, still require numerical approximation. Printing more digits does not prove that those digits are accurate.
Continue in the same session through sections 2–8. Section 9 starts a separate session with a saved database.

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
-- => 24 km h^-1
```

`h^-1` means “per hour.” Metron divides both the values and their units. The `to` expression chooses the units used to display the result.

Try another display unit:

```text
speed to m/s
-- => 6.6666666666666666666… m s^-1
```

The result starts with `6.6666666666666666666… m s^-1`. Metron retains the exact fraction internally. The ellipsis means that the decimal display continues beyond the printed digits.

### Make the formula reusable

A function takes inputs and calculates a result. Define one that takes both distance and speed:

```text
let travelTime distance speed = distance / speed
travelTime (18 km) speed to min
-- => 45 min
travelTime (18 km) (15 km/h) to min
-- => 72 min
```

The two calls give `45 min` and `72 min`. The parameter named `speed` belongs to the function. Each call supplies its value explicitly.

Parentheses keep a quantity together when you pass it to a function. Write `travelTime (18 km) speed`, rather than `travelTime 18 km speed`.

You can reuse the same approach for energy:

```text
let kineticEnergy mass speed = mass * speed^2 / 2
kineticEnergy (80 kg) (18 km/h) to J
-- => 1000 J
```

This gives `1000 J`. The calculation includes the conversion from kilometers per hour to meters per second.

### Let the units catch mistakes

A dimension describes a physical kind, such as length or time. Different units can describe the same dimension. Meters and kilometers are both lengths.

Try this deliberate mistake:

```text
1 m + 1 s
-- => Type error: length and time cannot be added (summary).
```

Metron refuses it because length and time cannot be added. Multiplication and division can combine dimensions, as they do in the speed and energy formulas.

Use `:type` to inspect the information Metron infers:

```text
:type speed
-- => Num (m/s)
:type travelTime
-- => forall s d d1. Tensor s d -> Num d1 -> Tensor s (d/d1)
```

A function can have a more general type than its example calls suggest. Metron infers relationships between input and output dimensions instead of assuming every argument is a plain number.

Here, `s` describes the first input's shape, while `d` and `d1` describe the inputs' dimensions. Dividing by a scalar preserves that shape and divides the dimensions.

### Define a useful unit

Suppose one lap of your track is 400 meters:

```text
unit lap = 400 m
5 lap to km
-- => 2 km
```

The result is `2 km`. A unit definition makes `lap` available as a quantity suffix and as a conversion target. Ordinary values use `let` instead.

For a calculated number, attach a unit with multiplication, as in `(2 + 3) * km`. When passing a unit-sized amount to a function, write `1 km`. A bare unit is not a general value that you can pass around by itself.

At multiplication and division, a bare unit means one unit-sized amount:

```text
5 * km to m
-- => 5000 m
4 km / 2 km
-- => 2
4 km / km
-- => 4
```

These give `5000 m`, `2`, and `4`. A quantity suffix keeps each number and its unit together. For a compound unit, write `5 km/h` or `5 * (km/h)`.

## 3. Follow measurement uncertainty

Suppose you need edging for a rectangular board. Its measured length is 2 meters and its width is 1 meter, each with some uncertainty. Calculate the total edging and how much its length varies.

Describe a measurement with a probability distribution, a model of possible values and their probabilities. A normal distribution
uses a mean and a standard deviation. The standard deviation describes spread,
not a guaranteed maximum error.

```text
:set samples 1000
:set seed 1
let boardLength = sample (normal (2 m) (0.01 m))
let boardWidth = sample (normal (1 m) (0.005 m))
let perimeter = 2 * (boardLength + boardWidth)
perimeter
-- => 5.9773770050871360472… m (Monte Carlo: mean 6.00009711344… m, sd 0.0232502928741… m, outcome 95% [5.95344474321… m, 6.04522466963… m], 1000 input samples)
mean perimeter
-- => About 6 m.
sd perimeter
-- => About 0.0233 m with this seed and sample count.
```

An input realization is one set of sampled input values. Metron evaluates the formula for 1,000 realizations. The report gives a sample mean, sample standard deviation and central 95% outcome interval.
The mean is near 6 m and the standard deviation is near 0.0224 m.
These estimates vary with the seed and sample count.
The outcome interval describes simulated measurements, not confidence in the mean.

The number before the report is the ordinary value, not the sample mean.
Use `mean perimeter` for the mean and `sd perimeter` for the sample standard deviation.
`mean` is a function, so you can use it inside another expression, such as `mean perimeter / 2`.

The seed selects a reproducible random sequence. With the same code, configuration and seed, repeated evaluations reproduce their draws.
Change the seed to explore another finite sample. Increase `samples` to estimate the distribution from more draws.
Neither change gives a guaranteed bound on all possible outcomes.

The same measurements also tell you how much surface needs paint:

```text
let boardArea = boardLength * boardWidth
mean boardArea to m^2
-- => About 2 m^2.
sd boardArea to m^2
-- => 0.0147 m^2 (rounded).
```

Multiplication carries the sampled measurements through the area formula. You can reuse the inputs without defining a separate uncertainty formula for area.

### Keep shared measurements shared

```text
boardLength == boardLength
-- => true
sd (boardLength - boardLength)
-- => 0 m
```

The results are `true` and `0 m`. Both uses refer to the same sampled input.
Two separate sample declarations have independent latent draws.
A sample site is one place in the source that calls `sample`.
A site inside a function reuses its random draw across calls.
Repeatedly calling that function does not create independent measurements.
Use distinct sample sites when you need independent inputs.

A uniform distribution is useful when your measurement model assigns equal
probability across an interval:

```text
let clearance = sample (uniform (0.9 mm) (1.1 mm))
clearance
-- => 0.97502617066127309011… mm (Monte Carlo: mean 1.00010990720… mm, sd 0.0583593015156… mm, outcome 95% [0.905578421044… mm, 1.09501816390… mm], 1000 input samples)
```

Distribution parameters must be deterministic scalars with matching dimensions.
You cannot pass another sampled value as a distribution parameter.
Build correlated quantities from shared sampled inputs instead.

Standard deviation must be nonnegative. A uniform distribution needs its lower endpoint first.
Equal endpoints and a zero standard deviation are valid.
A distribution is a description that you can name before drawing from it:

```text
let sensorModel = normal (10 m) (0.2 m)
let sensorA = sample sensorModel
let sensorB = sample sensorModel
sd (sensorA - sensorB)
-- => About 0.294 m.
```

The two sample sites draw independently from the same model.
That model predicts a standard deviation of about `0.283 m` for their difference.
The finite sample estimates it at about `0.294 m` with this seed and count.
Reusing `sensorA` instead of sampling again preserves its correlation with quantities derived from it.

### Measure correlation

```text
let reading = sample (normal (10 m) (0.2 m))
let doubled = 2 * reading
sd doubled
-- => About 0.408 m.
covariance [reading, doubled]
-- => [0.0416, 0.0831; 0.0831, 0.1663] m^2 (rounded).
```

The standard deviation is near 0.4 m. The covariance matrix is near
`[0.04, 0.08; 0.08, 0.16] m^2`.
Metron calculates these statistics from paired input realizations, with denominator N−1.

### Explore floating-point sensitivity separately

Stochastic rounding repeats a double calculation with perturbed rounding choices.
It measures sensitivity to that perturbation model.

```text
:set arithmetic double
:set roundingAnalysis stochastic
:set roundingSamples 8
(1e16 + 1) - 1e16
-- => 0 (stochastic rounding: typical spread 1.0690449676496976, RMS displacement 1.4142135623730951, 8 repetitions per input; distribution generation excluded; libm perturbations are heuristic)
```

The ordinary double result is 0. Diagnostic repetitions can produce different
results, such as 2. The report separates their spread from their displacement
relative to the ordinary result. Neither value is a guaranteed numerical bound.

The typical spread summarizes variation among repetitions of each fixed input.
RMS displacement summarizes their distance from the ordinary result.
If the repetitions agree, the report says “no variation observed.” This does not prove exactness.

Run both kinds of sampling together:

```text
perimeter
-- => 5.977377005087137 m (Monte Carlo: mean 6.000097113444719 m, sd 0.02325029287419864 m, outcome 95% [5.953444743218191 m, 6.045224669639076 m]; 1000 input samples; stochastic rounding: typical spread 5.392138636769817e-16 m, RMS displacement 7.397785161770224e-16 m, 8 repetitions per input; distribution generation excluded; libm perturbations are heuristic)
```

This report contains input statistics and rounding diagnostics in separate fields.
With 1,000 input draws and eight repetitions, it evaluates 1,000 ordinary outcomes and 8,000 diagnostic outcomes.

For sampled inputs, Metron fixes each input realization across its rounding
repetitions. Only ordinary runs contribute to the input statistics.
Distribution generation and parameter evaluation are excluded from the diagnostic.
Elementary functions use a heuristic perturbation of one representable step.
This models rounding sensitivity rather than every source of numerical error.
Statistics such as `mean`, `sd` and `covariance` reject rounding analysis of their own calculations.
Turn the diagnostic off before requesting those statistics.

Return to the arithmetic used by the remaining examples:

```text
:set roundingAnalysis off
:set arithmetic rational
```

### Choose the calculation controls

Use `:set` without arguments to inspect the configuration.
Arithmetic selects the number representation. Propagation selects how uncertain inputs pass through the calculation.
Only Monte Carlo propagation is currently supported.

| Control | Default | Accepted values and meaning |
| --- | --- | --- |
| `arithmetic` | `double` | `rational` or `double`. Rational operations preserve exact fractions. |
| `propagation` | `montecarlo` | `montecarlo`. Input draws pass through the complete expression. |
| `samples` | `10000` | 1–100000 input draws. Standard deviation and covariance need at least two. |
| `seed` | `1` | A nonnegative integer that selects the random sequence. |
| `roundingAnalysis` | `off` | `off` or `stochastic`. The latter requires double arithmetic. |
| `roundingSamples` | `8` | 2–1000 repetitions per fixed input when analysis is on. |
| `precision` | `20` | Controls rational approximations and decimal display, not double precision. |
| `cores` | Runtime's available cores | A positive worker count for input-only double batches. |

Changing `cores` does not change the draws or reports. Rational sampling and grouped rounding currently run serially.
Input-only double calculations can use concurrent batches. Expressions containing cross-input statistics, such as `sd`, use one evaluation instead.
The executable enables the available logical cores at startup. Use `:set cores 4` to request four batches.
Grouped rounding execution is capped at one million runs and also obeys the component limit.
Step, memory and time limits can refuse a calculation before it finishes.

The command line accepts the same configuration:

```sh
nix run . -- --no-codebase --set arithmetic double --set samples 1000 --set seed 1 'sample (normal (10 m) (0.2 m))'
```

Rounding analysis starts off. To return from stochastic analysis to rational arithmetic, turn the analysis off first, as shown above.

## 4. Work with vectors and matrices

A vector is an ordered set of components. Use square brackets to write one. The following velocity has components of 3, 4, and 0 meters per second:

```text
let velocity = [3, 4, 0] m/s
let elapsed = 10 s
let displacement = velocity * elapsed
displacement
-- => [30, 40, 0] m
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
-- => [3, 4; 6, 8]
a · b
-- => 11
a ⊙ b
-- => [3, 8]
```

The results are a matrix `[3, 4; 6, 8]`, a number `11`, and a vector `[3, 8]`, respectively. In ASCII, the same expressions are `a * b`, `a @ b`, and `a .* b`.

The wedge product stores the matrix `a ⊗ b - b ⊗ a`. An antisymmetric matrix changes sign when its rows and columns are exchanged. In three dimensions, applying `star` to this matrix gives the cross product:

```text
let u = [1, 0, 0]
let v = [0, 1, 0]
u ∧ v
-- => [0, 1, 0; -1, 0, 0; 0, 0, 0]
u × v
-- => [0, 0, 1]
⋆ (u ∧ v)
-- => [0, 0, 1]
```

The wedge result is `[0, 1, 0; -1, 0, 0; 0, 0, 0]`. Both remaining expressions give `[0, 0, 1]`. In ASCII, write `u /\ v`, `u >< v`, and `star (u /\ v)`.

The wedge product works with equal-length vectors beyond three dimensions. The cross product and this `star` operation are specific to three dimensions. Here, `∧` means wedge, while boolean “and” uses `&&`.

These operations do not yet provide a full Grassmann algebra with arbitrary grades.
`star` requires an alternating matrix, with zero diagonal and opposite entries across that diagonal.
Constructing it with `wedge` preserves that structure in every sampled realization.

### Calculate speed and work

A dot product multiplies matching components and adds the results. Metron writes it as `·`. The dot product of a vector with itself gives its squared magnitude:

```text
sqrt (velocity · velocity) to m/s
-- => 5 m s^-1
```

The result is `5 m s^-1`. The units follow the square and square root operations.

Work is the dot product of force and displacement:

```text
let force = [10, 0, 0] N
force · displacement to J
-- => 300 J
```

The result is `300 J`. Only the displacement component in the force's direction contributes.

The cross product answers a different question: how does a force turn an object about a pivot? Torque is this turning effect. Apply the same force half a meter along the second axis from the pivot:

```text
let leverArm = [0, 0.5, 0] m
let torque = leverArm × force
torque to N*m
-- => [0, 0, -5] N m
```

The negative third component gives the direction by the right-hand rule. Torque and work share physical dimensions, but torque is a vector here and work is a scalar.

### Apply a matrix

Semicolons separate a matrix's rows. The `@` operator performs matrix multiplication:

```text
let swap = [0, 1, 0; 1, 0, 0; 0, 0, 1]
swap @ displacement
-- => [40, 30, 0] m
```

This gives `[40, 30, 0] m`, with the first two components exchanged. This matrix is dimensionless, so the result retains the displacement's units.

You can also solve a small linear system using an inverse:

```text
let coefficients = [2, 0; 0, 4]
inverse coefficients @ [6, 8]
-- => [3, 2]
```

This solves `coefficients @ x = [6, 8]` for `x`. An inverse requires a suitable square matrix and can fail for a singular matrix.

Tensors extend vectors and matrices to more axes. Metron tracks their shapes and dimensions. Shape mistakes, such as incompatible matrix sizes, are errors rather than implicit resizing.

## 5. Separate points from changes

A point describes a position relative to an origin. A change describes a difference between points. This distinction matters for temperature scales and coordinate frames.

### Start with temperature

Celsius and Fahrenheit have different zero points. Convert a temperature point with `to`:

```text
20 degC to degF
-- => 68 degF
```

The result is `68 degF`. Find a temperature change with `.-`, or add a change to a point with `.+`:

```text
25 degC .- 20 degC
-- => 5 K
20 degC .+ (5 K)
-- => 25 degC
```

These give `5 K` and `25 degC`. A temperature point and a temperature change have different roles. Adding two Celsius points with ordinary `+` is rejected.

The same point operations have Unicode spellings:

| Operation | Unicode | ASCII | Result |
| --- | --- | --- | --- |
| Move a point by a displacement | `p ⊞ v` | `p .+ v` | A point |
| Find the displacement between points | `p ⊟ q` | `p .- q` | A displacement from `q` to `p` |

```text
20 degC ⊞ (5 K)
-- => 25 degC
25 degC ⊟ 20 degC
-- => 5 K
```

These give `25 degC` and `5 K`.
Type `\boxplus` or `\boxminus`, then press TAB, to enter the symbols in the REPL.
With `:set unicode on`, Metron prints these spellings. Both forms have the precedence of ordinary addition and subtraction.

Conversions chain from left to right. `20 degC to degF to kelvin` converts to Fahrenheit first and then to kelvin, and gives `293.15 kelvin`.

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
-- => [3, 1, 0] room
```

The result is `[3, 1, 0] room`. The conversion includes the bench's origin offset.

To place a calculated amount, use `pointAt`. It measures the amount from the chart's origin, along the chart's axes:

```text
pointAt bench ([0.5, 0, 0] m * 2)
-- => [1, 0, 0] bench
pointAt bench ([0.5, 0, 0] m * 2) to room
-- => [3, 1, 0] room
```

These give `[1, 0, 0] bench` and `[3, 1, 0] room`. A named vector, such as `let reach = [1, 0, 0] m`, has no axes of its own. Give it the bench's axes first: `pointAt bench (withAxes bench reach)`.

Find a displacement in bench coordinates and use it to move a point:

```text
let shift = [2, 0, 0] bench .- [1, 0, 0] bench
shift
-- => [1, 0, 0] m
([1, 0, 0] bench .+ shift) to room
-- => [4, 1, 0] room
```

The displacement prints as `[1, 0, 0] m`. The moved point becomes `[4, 1, 0] room`. A displacement does not include the chart's origin offset.

### Rotate the axes

A rotated chart changes the directions of its axes. Define a chart turned 90 degrees around the third axis:

```text
chart turned on room by rotz (90 deg)
[1, 0, 0] turned to room
-- => About [0, 1, 0] room.
```

The result is approximately `[0, 1, 0] room`. Rotation calculations can print tiny residuals near zero. Those values reflect numerical approximation.

Now convert a displacement between the same axes:

```text
let turnDelta = [1, 0, 0] turned .- [0, 0, 0] turned
:type turnDelta
-- => Vec turned m
turnDelta from turned to room
-- => About [0, 1, 0] m.
```

The type of `turnDelta` is `Vec turned m`. The converted result is approximately `[0, 1, 0] m`, and its type is `Vec Workshop m`: it now lies along the target's axes, although both display only meters.

Use `point to chart` for point conversion. Use `delta from source to target` when explicitly converting a displacement between charts. Convert differently oriented displacements to matching axes before adding them.

Do not assume that matching printed units imply matching coordinate systems. Two vectors can both print in meters while referring to different axes or different spaces.

## 6. Process several rides

A list is a sequence of values. Lists use braces, while tensors use square brackets. Use `map` to apply a function to each list element:

```text
let times = map (\d -> travelTime d (18 km/h)) {3 km, 6 km, 9 km}
map (\t -> t to min) times
-- => {10 min, 20 min, 30 min}
```

The rides take 10, 20, and 30 minutes. Converting each time makes the list easier to read. The expression `\d -> ...` is a function written without giving it a name.

Use `foldl` to combine the results from left to right:

```text
foldl (\total time -> total + time) (0 s) times to min
-- => 60 min
```

This gives `60 min`. The initial total is `0 s`, with a time unit. Each step adds one time to that total.

## 7. Give your data and formulas structure

A record groups named fields into one value. Define a ride with a distance and a duration:

```text
data Ride = Ride {distance :: Num m, duration :: Num s}
let morning = Ride {distance = 12 km, duration = 30 min}
let averageSpeed ride = ride.distance / ride.duration
averageSpeed morning to km/h
-- => 24 km h^-1
```

The result is `24 km h^-1`. The field types require length and time, but they do not require a particular display unit. A distance in kilometers fits `Num m` because both describe length.

### Choose between named cases

A data type can also describe a choice. Here, a pace is either `Brisk` or `Steady`:

```text
data Pace = Brisk | Steady
let paceLabel ride = if averageSpeed ride > 20 km/h then Brisk else Steady
paceLabel morning
-- => Brisk
```

The result is `Brisk`. The `if` expression chooses a value based on a condition. With sampled inputs, each realization takes its own branch:

```text
let uncertainRide = Ride {distance = sample (normal (10 km) (0.5 km)), duration = 30 min}
paceLabel uncertainRide
-- => Brisk and Steady outcome table, about half the draws in each case.
```

The result includes an outcome table for `Brisk` and `Steady`. Their proportions estimate the chance of exceeding the 20 km/h threshold under this input model.
Rounding-driven branch changes, when enabled, have separate diagnostic counts.

Use `case` to calculate a result for each named choice:

```text
let restMinutes pace = case pace of Brisk -> 10 min; Steady -> 5 min
restMinutes (paceLabel morning)
-- => 10 min
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
-- => 45 min
```

The result is `45 min`. Commands such as `:ls cycling` and `:view cycling.travelTime` help you inspect the group.

You can use `:use cycling` to make its names available without the prefix; Metron confirms with `stored use cycling`. Existing local names can affect lookup, so full names remain useful when names overlap.

## 8. Compute an orbit

The `astro` library holds orbital mechanics. It is not in use by default. Make its names available, choose a set of constants for the Earth, and add the two-body functions:

```text
:use astro
:use astro.wgs84
:use astro.kepler
earth.mu
-- => 398600441800000 m^3 s^-2
```

Each `:use` prints a confirmation, such as `stored use astro`. The last line prints `398600441800000 m^3 s^-2`. This is the Earth's gravitational parameter, GM, in the WGS 84 system that GPS uses. A set of constants is a namespace. `astro.iers2010`, `astro.iau2015` and `astro.de440` define the same names from other sources.

### Find the orbit of a satellite

A position and a velocity describe a satellite at one moment. This example is from Vallado's *Fundamentals of Astrodynamics and Applications*, example 2-5:

```text
let r0 = [6524.834, 6862.875, 6448.296] km
let v0 = [4.901327, 5.533756, -1.976341] km/s
let orbit = fromState earth r0 v0
orbit.e
-- => 0.83285339848752133549…
orbit.i to deg
-- => 87.869126177026452698… deg
period earth orbit.a to h
-- => 18.982893721345285847… h
```

The eccentricity is close to one, so the orbit is a long ellipse. Its inclination is nearly 90 degrees, taking it close to the poles. One revolution takes about 19 hours. The function names the Earth as its first argument, so the constants come from one place.

Move the satellite 40 minutes along its orbit, and convert it back to a position:

```text
let later = propagate earth orbit (40 min)
later.nu to deg
-- => 127.19430471529450586… deg
fst (toState earth later) to km
-- => [14937.7215, 16543.3922, -225.1884] km (rounded).
```

The angle from the closest point of the orbit grows from about 92° to 127°. The position remains in the same coordinate axes as the original state.

### See how far a solver went

`propagate` solves Kepler's equation with 12 Newton steps. It does not attach a bound for the remaining solver error.
A residual measures how far the result misses the original equation. Vallado's example 2-1 asks for the eccentric anomaly:

```text
meanToEccentric 0.4 (235.4 deg) to deg
-- => 220.51207476752206740… deg
let ea = meanToEccentric 0.4 (235.4 deg)
eccentricToMean 0.4 ea - 235.4 deg
-- => About -4.37e-37 deg.
```

The first result is approximately 220.512074767522 degrees. The second expression checks the solver's residual. A small residual is useful evidence, but it does not certify every displayed digit.

A measured input passes its uncertainty through the solver:

```text
:set arithmetic double
meanToEccentric 0.4 (sample (normal (235.4 deg) (0.01 deg))) to deg
-- => 220.51372965014176 deg (Monte Carlo: mean 220.51205436334467 deg, sd 0.007511635643720007 deg, outcome 95% [220.49717765127667 deg, 220.52637099774964 deg]; 1000 input samples)
:set arithmetic rational
```

Double arithmetic reduces the cost of the repeated solver calculations.
The sample mean is near 220.5121 degrees and the standard deviation is near 0.0077 degrees.
Input sampling does not measure solver truncation error or prove convergence for every orbit.

### Plan a transfer

A Hohmann transfer moves a satellite between two circular orbits with two burns. Vallado's example 6-1 goes from a low orbit to the geostationary altitude:

```text
:use astro.maneuver
let leo = earth.radius + 191.34411 km
let geo = earth.radius + 35781.34857 km
let climb = hohmann earth leo geo
climb.dv1 to km/s
-- => 2.4570375641775748610… km s^-1
climb.dv2 to km/s
-- => 1.4781866251255600022… km s^-1
total climb to km/s
-- => 3.9352241893031348632… km s^-1
climb.tof to h
-- => 5.2567133281852289025… h
```

The first burn enters the transfer orbit. The second burn makes the destination orbit circular. Together they require about 3.94 kilometers per second of velocity change, with about 5.26 hours between burns.

### Change the constants

A full name selects another set without a new `:use`:

```text
period iau2015.earth (7000 km) to min
-- => 97.141949054922148437… min
period earth (7000 km) to min
-- => 97.141943961433593065… min
```

These give `97.141949054922148437… min` with the IAU 2015 value and `97.141943961433593065… min` with WGS 84. If you enter `:use astro.iau2015` instead, Metron refuses it: `earth` would then name two bodies, and the pending definitions use `earth`.

## 9. Start a saved database

Quit the practice session with `:quit`. From the project directory, start a separate store at a new path:

```sh
nix run . -- --codebase /tmp/metron-learning-store
```

If that directory already contains earlier work, choose a different path. This tutorial uses `/tmp` for practice, so the operating system can remove it later. Use a durable directory for work you want to keep.

The database is also called a codebase. It stores definitions and the names that refer to them. It is a directory of files rather than a separate database server.

Create some definitions:

```text
:set arithmetic rational
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

## 10. Understand content-based identity

A hash is an identifier calculated from a definition's content. Metron uses hashes to identify definitions and their dependencies. Names are labels that point to those identities.

### Two names can identify one definition

Compare the two values:

```text
:hash five
-- => #ico3k
:hash alsoFive
-- => #ico3k
```

Both commands print the same hash. Compare the functions too:

```text
:hash addOne
-- => #uija9
:hash increment
-- => #uija9
```

These also share a hash. Renaming a function parameter from `x` to `y` does not change its meaning or its identity. The parameter names help people read the source, but do not distinguish these definitions.

The hashes shown here come from this version of Metron. Language changes can change hashes, so use the identifiers printed in your own session.

You can add another label explicitly:

```text
:alias fiveAgain five
fiveAgain
-- => 5
```

The result is `5`. The alias gives an existing definition another name. It does not copy or recalculate its body.

To inspect its names, run `:hash five`, then pass the printed identifier to `:names`. For example, if the output is `#ico3k`, enter `:names #ico3k`. Use the hash from your own session.

### Equal results do not guarantee equal hashes

Define another expression that evaluates to five:

```text
let computedFive = 2 + 3
computedFive
-- => 5
:hash computedFive
-- => #8vm89
:hash five
-- => #ico3k
```

The result is still `5`, but these definitions have different hashes. Metron identifies stored expressions, not every mathematical equivalence between them. It does not prove that two arbitrary programs always produce the same result.

Save the new definition before continuing:

```text
:add
```

A hash also includes the identities of referenced definitions. Changing a dependency creates a new identity for an upgraded dependent, even when its displayed source still uses the same names.

The arithmetic mode, sample count and seed belong to the evaluation configuration, not the stored term hash.
Changing them can change a result without changing its definition's identity.
Record the configuration alongside results that you need to reproduce.

## 11. Upgrade a function deliberately

Create a travel-time function and a saved calculation that uses it:

```text
let journeyTime distance speed = distance / speed
let commute = journeyTime (12 km) (24 km/h)
:add
commute to min
-- => 30 min
```

The result is `30 min`. The saved `commute` refers to this specific version of `journeyTime`. It does not look up whichever definition happens to have that name each time it runs.

Inspect the relationship:

```text
:hash journeyTime
-- => #ma5cf
:hash commute
-- => #2c6m8
:dependents journeyTime
-- => commute
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
-- => 35 min
commute to min
-- => 30 min
```

The results are `35 min` and `30 min`. This difference is intentional. Updating a label without upgrading dependents preserves the saved calculation's original dependency.

Inspect the old reference and the history:

```text
:view commute
-- => commute = journeyTime#ma5cf (12 km) (24 km / h)
:todo
-- => stale: commute uses journeyTime#ma5cf (use :upgrade journeyTime)
:history journeyTime
-- => #1ilgc  (current)
--    #ma5cf
```

The view contains a reference resembling `journeyTime#ma5cf`. The suffix identifies the older version. The history lists the current version first, followed by earlier versions.

You can call that older function directly. Replace `ma5cf` below with the old hash from your own history if it differs:

```text
journeyTime#ma5cf (12 km) (24 km/h) to min
-- => 30 min
```

The result is `30 min`, even though a call to the current `journeyTime` gives `35 min`. Keep the name and `#` together. A named hash searches versions previously or currently associated with that name.

A bare hash searches the stored definitions without requiring a name:

```text
#ma5cf (12 km) (24 km/h) to min
-- => 30 min
```

This also gives `30 min`. A prefix must identify one definition, or Metron reports the ambiguity and shows the full matching hashes. A bare hash that refers to a recursive function group needs a member suffix, such as `#dlcnc.0`, because the hash names the whole group; `:hash` prints it with the suffix. A named reference such as `fact#dlcnc` needs no suffix.

When passing a bare hash as a function argument, put it in parentheses, as in `f (#hash)`. This distinguishes the reference from a trailing measurement label such as `sample (normal 5 1) #sensor`. A glued `name#hash` is always a version reference, so separate measurement labels from preceding names with whitespace.

These expressions select the old content when they are resolved. A saved definition made with them still participates in the normal upgrade rules. Selecting a version does not create a permanent exemption from `:upgrade` or `:update`.

The todo command identifies `commute` as stale and suggests an upgrade. Here, “stale” means that a newer dependency version is available. It does not mean that the original calculation is invalid.

### Upgrade the saved calculation

Move the dependent calculation to the new function:

```text
:upgrade journeyTime
commute to min
-- => 35 min
:hash commute
-- => #l75j3
:todo
-- => nothing to do
```

The result is now `35 min`. The hash of `commute` changes because its dependency changes. The todo command now reports `nothing to do`.

The upgrade creates a new dependent definition. It does not overwrite the old content under the old hash. The name `commute` moves to the upgraded definition.

### Use the default automatic upgrade

Now increase preparation time to ten minutes:

```text
let journeyTime distance speed = distance / speed + 10 min
:update
commute to min
-- => 40 min
:history commute
```

The result is `40 min`. Plain `:update` also attempts to upgrade dependents, so no separate `:upgrade` command is needed in this example. The history retains the earlier identities of `commute`.

Changes that make dependent definitions ill-typed can leave unresolved work. Use `:todo` after an update to inspect what remains. Successful propagation in this example does not mean every possible replacement is compatible.

## 12. Reopen and inspect the store

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

The current format is 13. Metron refuses earlier store formats and provides no automatic migration.
Use source written for the current language to create a new store.

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
-- => 40 min
```

The result is `40 min`. Loading source gives you definitions to work with. In a saved session, use `:add` or `:update` to accept them as appropriate.

For the full language reference, read [the design document](doc/design.md). For the implementation model, read [the core overview](doc/core.md). The [README](README.md) provides a shorter introduction.

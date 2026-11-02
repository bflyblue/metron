# Metron

Metron is a calculator and small programming language for calculations with physical quantities. You can work with distances, times, temperatures, and other measurements directly, with their units attached.

Use it for a quick conversion, an engineering estimate, or a reusable physics calculation. Metron checks physical dimensions and catches mistakes such as adding a length to a time.

Describe uncertain inputs with probability distributions. Monte Carlo sampling runs your formula with many input draws. Separate stochastic rounding diagnostics explore sensitivity to floating-point rounding. Neither method gives a guaranteed error bound.

The project is a proof of concept, written in Haskell. The language and storage format can change, and old saved data has no migration guarantee.

Metron uses the [MIT license](LICENSE). You can use, modify, and redistribute it, including commercially, with the copyright and license notice retained.

## What can you use it for?

Metron supports tasks such as:

- Converting measurements and calculating rates, areas, energies, and other physical quantities.
- Exploring how measurement uncertainty affects a result.
- Working with positions, velocities, and rotations in physics calculations.
- Building a library of formulas that you can inspect, reuse, and revise.

## Try it

With [Nix](https://nixos.org/download/) installed, run this command from the project directory:

```sh
nix run . -- --no-codebase
```

This opens an interactive calculator. The `--no-codebase` option keeps the session in memory without creating a saved store. Enter `:help` for commands or `:quit` to exit.

For a single calculation, pass an expression:

```sh
nix run . -- --no-codebase '5 km to m'
```

The result is `5000 m`. The executable is called `metron`, so an installed copy accepts the same arguments.

## A short example: planning a ride

Suppose you cycle 12 kilometers in 30 minutes. How long will an 18-kilometer route take at the same speed?

Enter these lines in the interactive calculator. Comments beginning with `-- =>` show results, so you can copy the whole block.

```text
:set arithmetic rational
let distance = 12 km
let duration = 30 min
let speed = distance / duration

speed to km/h
-- => 24 km h^-1

let travelTime distance speed = distance / speed
travelTime (18 km) speed to min
-- => 45 min

travelTime (18 km) (15 km/h) to min
-- => 72 min
```

Use `let` to define a value or function. Parentheses keep a quantity together when passing it to a function. The units follow the calculation: distance divided by speed gives time. The notation `h^-1` means “per hour.”

Rational arithmetic preserves exact fractions. Double arithmetic, which uses fixed-precision floating-point numbers, is the default.

```text
speed to m/s
-- => 6.6666666666666666666… m s^-1
```

The ellipsis marks a decimal that continues. Internally, this rational result is exactly 20/3 meters per second.

### What if the route length is uncertain?

Suppose the route estimate has a normal distribution with a mean of 18 kilometers and a standard deviation of 0.3 kilometers:

```text
:set samples 1000
:set seed 1
let routeDistance = sample (normal (18 km) (0.3 km))
let arrivalTime = travelTime routeDistance speed

arrivalTime to min
-- => 44.863475507699178832… min (Monte Carlo: mean 45.0084226974… min, sd 0.740787289689… min, outcome 95% [43.5287705890… min, 46.4427261886… min], 1000 input samples)

mean arrivalTime to min
-- => 45.0084 min (rounded).
sd arrivalTime to min
-- => 0.7408 min (rounded).

sd (arrivalTime - arrivalTime) to min
-- => 0 min
```

The same function now estimates a distribution of journey times. The block includes the actual report for this session. Results vary with the seed and sample count.

The leading value, about 44.86 minutes, is the ordinary result from one input realization. The `mean` summarizes all 1,000 draws. The `sd` measures their spread. The `outcome 95%` interval contains the central 95% of simulated journey times. It is neither a guaranteed bound nor a confidence interval for the mean.

The input model predicts a mean of 45 minutes and a standard deviation of 0.75 minutes. A finite sample gives estimates near those values.

Reusing `arrivalTime` reuses the same input draws, so subtracting it from itself cancels every draw. Separate `sample` sites describe independent inputs.

## Explore rounding separately

Ordinary double arithmetic rounds each operation to a representable number. For example, adding 1 to `1e16` loses that increment:

```text
:set arithmetic double
(1e16 + 1) - 1e16
-- => 0
:set roundingAnalysis stochastic
:set roundingSamples 8
(1e16 + 1) - 1e16
-- => 0, plus rounding diagnostics (rounded):
--    typical spread 1.0690, RMS displacement 1.4142.
:set roundingAnalysis off
```

The ordinary result stays `0`. The second report adds diagnostics from eight runs with perturbed rounding choices. These runs can expose results such as `2`.

For sampled inputs, Metron repeats each fixed input draw and reports rounding variation separately from input variation. The ordinary runs alone determine the input statistics. This diagnostic does not certify accuracy or correct the ordinary result.

The main controls are:

| Control | Default | Purpose |
| --- | --- | --- |
| `:set arithmetic rational` or `double` | `double` | Select the number representation. |
| `:set propagation montecarlo` | `montecarlo` | Select the supported input propagation method. |
| `:set samples N` | `10000` | Set the number of input draws. |
| `:set seed N` | `1` | Select a reproducible random sequence. |
| `:set roundingAnalysis off` or `stochastic` | `off` | Enable double-only rounding diagnostics. |
| `:set roundingSamples R` | `8` | Set repetitions for each fixed input draw. |

Use `:set` to inspect the current configuration. Command-line calls accept the same controls through `--set NAME VALUE`.

## What Metron keeps track of

Metron carries more information than a number alone:

- Units and dimensions: It rejects `1 m + 1 s` because length and time cannot be added.
- Arithmetic: Choose rational or double arithmetic. Rational fractions stay exact. For example, `1 / 3 + 1 / 6` gives `0.5`.
- Uncertainty: Explicit normal and uniform inputs propagate through complete calculations using Monte Carlo sampling. Optional stochastic rounding analysis on doubles reports numerical sensitivity separately.
- Tensors: These are arrays of numbers, including vectors and matrices. They carry units too. For example, `[3, 4] m + [1, 2] m` gives `[4, 6] m`.
- Charts: These describe coordinate systems, including origins and rotated axes. They distinguish points from changes, so temperature scales and physical frames follow different rules from ordinary unit multiplication.
- Saved definitions: Definitions have identities based on their contents and dependencies. This supports history and explicit updates to related formulas.

Rational fractions stay exact under rational operations. Roots, trigonometric functions and normal random draws still require approximation. Increasing the display precision does not increase double precision.

For example, temperature points and temperature changes obey different rules:

```text
:set arithmetic rational
20 degC to degF
-- => 68 degF
25 degC ⊟ 20 degC
-- => 5 K
20 degC ⊞ (5 K)
-- => 25 degC
```

Use `.-` and `.+` for the ASCII spellings of `⊟` and `⊞`. Adding two Celsius points with ordinary `+` is rejected.

## Keeping your work

Start without `--no-codebase` to use a saved store. Metron uses a project-local `.metron/` directory if it finds one, or the user data directory otherwise. You can choose a store with `--codebase DIR`.

New definitions remain in a temporary workspace until you accept them with `:add`. Use `:update` for changes to saved definitions. Use `:export` and `:load` to work with text files, or run a file with `metron -f ride.metron`.

The current store format is 13. Earlier formats are refused. Recreate a store from source written for the current language.

For a guided introduction, follow the [tutorial](TUTORIAL.md), from basic calculations through saved definitions and function upgrades. For more detail, read the [project overview](doc/overview.md), the [language design](doc/design.md), the [implementation overview](doc/core.md), or the [changelog](CHANGELOG.md). The design document also contains planned work and open questions.

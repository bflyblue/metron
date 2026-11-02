# Metron

Metron is a calculator and small programming language for calculations with physical quantities. You can work with distances, times, temperatures, and other measurements directly, with their units attached.

Use it for a quick conversion, an engineering estimate, or a reusable physics calculation. Metron follows units and uncertainty through your formulas, and catches mistakes such as adding a length to a time.

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

Suppose you cycle 12 kilometers in 30 minutes. Enter these lines in the interactive calculator:

```text
:set arithmetic rational
let distance = 12 km
let duration = 30 min
let speed = distance / duration

speed to km/h
```

Metron prints `24 km h^-1`, which means 24 kilometers per hour. The units follow the calculation automatically. Use `to` to choose another unit:

```text
speed to m/s
```

The result starts with `6.6666666666666666666… m s^-1`. Metron keeps the exact fraction internally, even when its decimal display cannot fit on one line.

You can turn the calculation into a function that takes both distance and speed as inputs:

```text
let travelTime distance speed = distance / speed
travelTime (18 km) speed to min
```

The result is `45 min`. Use `let` to define a value or function. Put a quantity in parentheses when passing it to a function, as in `(18 km)`.

Now describe the distance as a normally distributed measurement, with a standard deviation of 0.1 kilometers:

```text
let measuredDistance = sample (normal (12 km) (0.1 km))
measuredDistance / duration to km/h
```

The sample mean is near 24 km/h and the sample standard deviation is near 0.2 km/h.
The report describes simulated outcomes. It does not give a guaranteed error bound.

## What Metron keeps track of

Metron carries more information than a number alone:

- Units and dimensions: It rejects `1 m + 1 s` because length and time cannot be added.
- Arithmetic: Choose rational or double arithmetic. Rational fractions stay exact. For example, `1 / 3 + 1 / 6` gives `0.5`.
- Uncertainty: Explicit normal and uniform inputs propagate through complete calculations using Monte Carlo sampling. Optional stochastic rounding analysis on doubles reports numerical sensitivity separately.
- Tensors: These are arrays of numbers, including vectors and matrices. They carry units too. For example, `[3, 4] m + [1, 2] m` gives `[4, 6] m`.
- Charts: These describe coordinate systems, including origins and rotated axes. They distinguish points from changes, so temperature scales and physical frames follow different rules from ordinary unit multiplication.
- Saved definitions: Definitions have identities based on their contents and dependencies. This supports history and explicit updates to related formulas.

Double arithmetic is the default. Use `:set arithmetic rational` for exact rational operations. Rational elementary functions use numerical approximations.

For a basic chart conversion, try `20 degC to degF`. The result is `68 degF`. Adding two Celsius temperature points is rejected, because their zero point is an offset rather than an absolute origin.

## Keeping your work

Start without `--no-codebase` to use a saved store. Metron uses a project-local `.metron/` directory if it finds one, or the user data directory otherwise. You can choose a store with `--codebase DIR`.

New definitions remain in a temporary workspace until you accept them with `:add`. Use `:update` for changes to saved definitions. Use `:export` and `:load` to work with text files, or run a file with `metron -f ride.metron`.

For a guided introduction, follow the [tutorial](TUTORIAL.md), from basic calculations through saved definitions and function upgrades. For more detail, read the [project overview](doc/overview.md), the [language design](doc/design.md), the [implementation overview](doc/core.md), or the [changelog](CHANGELOG.md). The design document also contains planned work and open questions.

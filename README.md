# Fractal Non-Closure

[![CI](https://github.com/LarsenClose/fractal_non_closure/actions/workflows/ci.yml/badge.svg)](https://github.com/LarsenClose/fractal_non_closure/actions/workflows/ci.yml)
![Lean](https://img.shields.io/badge/Lean-v4.31.0-blue)
![License](https://img.shields.io/badge/license-Apache--2.0-blue)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21272427.svg)](https://doi.org/10.5281/zenodo.21272427)

Lean 4 formal core for the paper *Fractal Non-Closure*.

This repository formalizes a small grammar for level-indexed closure. A base
dynamical system may remain open under its own operation while a lawful factor
reading closes one level up to an invariant law state. The formal point is not
that every such reading is substantively informative, but that lawfulness,
closure, and retention of distinctions are separate requirements.

The paper source is maintained separately from this Lean package. The paper is
archived at [doi:10.5281/zenodo.21272282](https://doi.org/10.5281/zenodo.21272282);
this formalization is archived at
[doi:10.5281/zenodo.21272427](https://doi.org/10.5281/zenodo.21272427). Citation
metadata is in [`CITATION.cff`](CITATION.cff).

## Build

This project uses Lean `v4.31.0` and Lake. It imports `Std` and has no Mathlib
dependency.

```sh
lake build --wfail
```

## Formal Core

The main file is [`FractalNonClosure/Core.lean`](FractalNonClosure/Core.lean).

The core definitions are:

- `RenormSystem`: a type of states with one distinguished operation.
- `ElementClosed`: finite terminal closure of an orbit to one element.
- `OrbitClosed`: finite eventual periodic closure of an orbit.
- `InstanceOpen`: absence of both terminal and finite periodic closure at the
  base level.
- `Factor`: a lawful reading into a second system, expressed by the commuting
  square `obs (step x) = law.step (obs x)`.
- `LawClosure`: factor-level closure to an invariant, nondegenerate law state.
- `OpenWithLawClosure`: the abstract target shape: base-level openness with
  law-level closure.

The principal calibration results are:

- `TerminalReading.onePointCalibration`: every system admits a one-point lawful
  reading if that reading is allowed.
- `TerminalReading.lawful_closed_collapsing_of_distinct`: lawfulness and
  law-level closure can coexist with total collapse of a base distinction.
- `Factor.lawClosed_of_universal_closesTo`: if the closure relation is declared
  universal, law closure is automatic once an invariant nondegenerate law state
  is available.
- `NatSucc.onePoint_factor_openWithLawClosure_zero`: pure escape to infinity
  satisfies the abstract target shape under the one-point reading.
- `LatchReading.openWithLawClosure_without_terminal_reading`: the target shape
  is also satisfiable by a non-terminal reading that retains a base distinction.

Together these results isolate the structural claim: a commuting square proves
lawfulness of a reading, not by itself the substantive adequacy of the reading
for a domain. Retention and nondegeneracy have to be supplied by the intended
mathematical context.

## Scope

This v1 formalizes the abstract scaffolding used by the paper. It does not
formalize Hausdorff dimension, scenery flow, tangent measures, or a specific
measure-theoretic fractal example. Those are the natural targets for later
extensions once the domain-specific collapse and nondegeneracy conditions are
chosen explicitly.

## Repository Hygiene

- CI builds with `lake build --wfail`.
- Generated Lake output is ignored.
- The public repository contains only the Lean package and project metadata.
- Paper drafts, manuscript build artifacts, and render scratch files live
  outside this repository.

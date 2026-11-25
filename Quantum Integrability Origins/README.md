# Quantum origins of NLS integrability

Nataša Pavlović, Matthew Rosenzweig, and Gigliola Staffilani

A Lean 4 formalization of the principal quantum-to-classical correspondence results for periodic defocusing cubic nonlinear Schrödinger dynamics, including a global canonical construction and its six-part correspondence theorem. The scope is the principal dependency set, not the entire mathematical report, *Quantum origins of periodic cubic NLS integrability: A comprehensive technical report* (10 November 2026).

Start with [the main theorem](QuantumNLS/MainTheoremR03.lean), `QuantumNLS.MainTheoremR03.thm_main`. For positive spatial period and positive coupling, it uses one sequence of occupation gauges and one active schedule, chosen before the profiles and test parameters, for the six clauses and evolved-state coherence. The precise hypotheses, tests and limiting statements are those in Lean. In particular, the statement does not separately establish nontriviality of the limiting generator.

## Build

Install Elan and run from this directory:

```sh
lake exe cache get
lake build
```

The pinned project toolchain is Lean 4.34.1. Mathlib and its dependencies are pinned in [lake-manifest.json](lake-manifest.json).

## Verification and scope

The portable project builds all 2,927 project modules with Lean 4.34.1. The release checks confirm the headline theorem’s statement and that its proof uses only the three standard axioms. The earlier independent kernel replay and the Comparator check of 34 selected roots are described separately in [Verification and errata](docs/VERIFICATION-AND-ERRATA.md).

## License

The original Lean code is available under the [Apache License, Version 2.0](LICENSE). Mathlib and its dependencies are pinned separately and retain their respective licenses and attribution. The source manuscript is not included.

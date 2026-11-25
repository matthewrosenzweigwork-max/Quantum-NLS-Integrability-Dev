# Fixed-period derivation

Nataša Pavlović, Matthew Rosenzweig, and Gigliola Staffilani

A Lean 4 formalization of selected results for the fixed-period nonlinear Schrödinger equation and its generalized Gibbs ensembles. The release includes three results for the Birkhoff coordinates and the flow: [Birkhoff conjugacy](LiebLiniger/FixedPeriod/Atomic/ALLS/TransCFinalMain.lean), [persistence in nonnegative Sobolev regularity](LiebLiniger/FixedPeriod/Atomic/ALLS/TransCFinalAP.lean), and [invariance of the actions](LiebLiniger/FixedPeriod/Atomic/ALLS/TransCFinalAP.lean). The Lean declarations specify the hypotheses and conclusions.

## Build

From this directory, with [elan](https://github.com/leanprover/elan) installed, run `lake exe cache get` and `lake build NlsGge Armstrong LiebLiniger`. The project uses Lean 4.34.1; `lake-manifest.json` pins Mathlib and its dependencies. This project is standalone and does not require a sibling checkout of the construction project.

## Scope and verification

The formalization covers a selection of manuscript results and does not formalize the whole paper. For the original retained selection, a frozen source tree passed a clean build and kernel replay, and Comparator checked 40 contracts for 24 retained results. Separately, the dependency closure of the three all-regularity results passed a clean build of 2,942 modules. Comparator checked exactly those three final statements against the approved statement text; kernel-replay and axiom-audit coverage was established by matching the resulting Lean objects to the audited objects. The [scope notes](docs/SCOPE.md) explain further limits.

The release tree passed an isolated build of all 3,608 modules. The exported declarations in all 3,608 compiled modules were checked for transitive axiom dependencies; only `propext`, `Classical.choice`, and `Quot.sound` occurred.

This is a reorganized source tree. The historical verification figures describe the pinned input snapshots, not a replay of every check on this tree.

## Errata and deviations

See [Errata and deviations](docs/ERRATA-AND-DEVIATIONS.md) and the [scope notes](docs/SCOPE.md).

## License

The original Lean code is available under [Apache-2.0](LICENSE). See [third-party attributions](THIRD_PARTY_NOTICES.md) for adapted material and the accompanying notices. No manuscript or private verification records are included.

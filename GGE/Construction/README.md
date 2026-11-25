# Periodic NLS generalized Gibbs ensembles: construction

Nataša Pavlović, Matthew Rosenzweig, and Gigliola Staffilani

This Lean 4 development accompanies the fixed-period construction of generalized Gibbs ensembles for the one-dimensional defocusing cubic nonlinear Schrödinger equation. It contains formal results on the finite-gap construction, Fourier approximation, and supporting spectral and measure-theoretic estimates. Check the precise hypotheses of each Lean declaration before applying it.

The reference is the 55-page fixed-period v2 manuscript, *Periodic NLS generalized Gibbs ensembles: fixed-period construction and the full-energy Fourier limit*. The manuscript is separate from this code export.

## Entry points

- [Finite-gap symplectic volume](NlsGge/ThirdConsultation/PDE/E01SymplecticVolume.lean): E01_finiteGap_symplectic_volume.
- [Trace formula through the fourth charge](NlsGge/Spectral/ActualTraceFormulaQ024E02_38.lean): actualTraceFormula_Q4_complex_E02_38.
- [Conditional lattice moment estimate](NlsGge/Hierarchy/ALTiltMeasure38.lean): alTilt_H2_moment_conditional38, with its explicit premises.

## Build

The entry point is NlsGge.lean. This source export keeps the dependencies of the retained results rather than every file in the development checkout.

Install Elan, then run these commands from this directory:

    lake exe cache get
    lake build NlsGge Armstrong

The toolchain is Lean v4.34.1. The dependency lock is lake-manifest.json; Mathlib is pinned to d13f23b723b8a846827a245b89c10fc7d3f11612.

## Scope

The spatial period is one. The all-charge lattice continuum limit and the thermodynamic limit are outside the scope of this development. The Lean statements distinguish convergence of densities in a common Gaussian space from total-variation convergence for finite-plane laws. The conditional partition-function statement retains its antecedents. The separate additive physical invariance result for the fourth charge is not included.

## Verification and licensing

This development covers a retained set of statements, not a formalization of the entire manuscript. The source revision underlying this release passed a fresh project build, exact-type and transitive-axiom audits, and independent Comparator checks on selected roots of the full development snapshot. The historical Comparator command and its full root list are not part of this export. The release tree passed an isolated build of all 3,828 Lean modules. A targeted check against the pinned Lean revision matched the theorem types and transitive axioms for all 268 declarations cited in the 62 release records. This was not a new Comparator run or independent kernel replay.

The original Lean code is licensed under [Apache License 2.0](LICENSE). This license does not cover the separately maintained manuscript. See [Third-party code](docs/THIRD-PARTY.md) for credits and license notices.

## Errata and deviations

See [Errata and deviations](docs/ERRATA-AND-DEVIATIONS.md) for external-source errata and the scope of the exported Lean statements.

import Mathlib
import QuantumNLS.RC05Statement

/-!
# RC05FreqCov: STATEMENT ONLY, the extra frequency-covariance conclusion of R-C05E2420 (proof-cited item 5b)

This module contains one DEFINITION and no theorem. `FreqCovCorollary` restates, as a corollary-shaped proposition, the frequency
covariance conclusion of R-877E839C `cor:global-frequency-covariance` (`compatibility.tex:158`) that the printed proof of
`thm:global-full-transform` cites (`source-text/chapters/global/main_theorem.tex`). It is NOT a displayed clause of the six-item
theorem `RC05Displayed.global_full_transform`, which does not import this module.

Nothing here is proved, accepted or claimed. The content is exactly the named input `RC05Statement.FreqCovInput` (R-877E839C,
unaccepted), in the existential form used by `RC05Main.FullTransform` item 5b: for every extending family and some frequency
family realizing the all-time rotation law of the physical flow, the frequency covariances `FreqCovClauses` hold.
A later proof must come from the accepted R-877E839C headline with an explicit adapter; the interface equivalence is not checked here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ENNReal Topology ComplexConjugate
open Filter Set Metric

namespace QuantumNLS.RC05FreqCov

open QuantumNLS.StrongSymplectic QuantumNLS.RC05Statement
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.D01LocalPrimitive (K)
open QuantumNLS.ActionTorus (PosL1)
open QuantumNLS.RF535Final (Local023Body)
open QuantumNLS.GlobalCompatR47a (Family)

/-- STATEMENT ONLY, UNPROVED, NOT ACCEPTED: for every period `L > 0`, the LOCAL-023 data and an extending family exist, and for every
extending family there is a frequency family `ν^{(κ)}` with the all-time rotation law of the physical flow at every coupling `κ > 0`
for which the printed frequency covariances `FreqCovClauses` hold (boost, reflection, scaling, conjugation, common phase, translation). -/
def FreqCovCorollary : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)], ∃ d CL : ℝ, 0 < d ∧ 0 ≤ CL ∧
    ∃ (Φl : ℝ → L2T L → K) (Ψl : ℝ → K → L2T L),
      Local023Body L d CL Φl Ψl ∧ (∃ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Family d Φl Ψl Φ Ψ) ∧
      ∀ (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L), Family d Φl Ψl Φ Ψ →
        ∃ ν : ℝ → ℤ → PosL1 → ℝ,
          (∀ (κ : ℝ) (hκ : 0 < κ), PhysicalFrequency hκ (Φ := Φ κ) (ν κ)) ∧ FreqCovClauses L ν

end QuantumNLS.RC05FreqCov

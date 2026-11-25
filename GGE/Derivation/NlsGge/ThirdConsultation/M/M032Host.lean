import Mathlib
import NlsGge.ThirdConsultation.M.MRound11Host
import NlsGge.ThirdConsultation.M.M021Host
import NlsGge.Atomic.G2.G2046

/-!
# M-032 host: `potentialTailEnergy`, `complexGapTailEnergy` (proof development, host; not self-reviewed)

Definitions only, verbatim from Pro round 14 (`PRO_DEFINITION_RESPONSE_FP80_14.md`, Cluster 4, namespace
`NlsGge.ThirdConsultation.MTwoMode` block).  `gap` is the landed `NlsGge.GKDefinitionDesign.gap` (G2-046 host).
-/

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace NlsGge.ThirdConsultation.MTwoMode

/-- Source Fourier tail R_N, including the reflected upper raw coefficient. -/
def potentialTailEnergy (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) (N : ℕ) : ℝ≥0∞ :=
  ∑' n : ℤ, if N ≤ n.natAbs then
    ENNReal.ofReal (w (2 * n) ^ 2 *
      (‖fourierPotential φ true (2 * n)‖ ^ 2 +
       ‖fourierPotential φ false (-2 * n)‖ ^ 2))
    else 0

/-- Complex gap length, not a real-gap length of a nonexistent realPhysical. -/
def complexGapTailEnergy (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) (N : ℕ) : ℝ≥0∞ :=
  ∑' n : ℤ, if N ≤ n.natAbs then
    ENNReal.ofReal (w (2 * n) ^ 2 *
      ‖NlsGge.GKDefinitionDesign.gap φ n‖ ^ 2)
    else 0

end NlsGge.ThirdConsultation.MTwoMode

end

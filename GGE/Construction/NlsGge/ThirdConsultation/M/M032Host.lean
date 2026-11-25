import Mathlib
import NlsGge.ThirdConsultation.M.MRound11Host
import NlsGge.ThirdConsultation.M.M021Host
import NlsGge.Atomic.G2.G2046

   
                                                                                                  

                                                                                                        
                                                                                                               
  

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

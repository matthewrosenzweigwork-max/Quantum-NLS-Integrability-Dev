import Mathlib
import NlsGge.ThirdConsultation.M.MRound11Host

set_option autoImplicit false
open scoped ENNReal

namespace NlsGge.ThirdConsultation.M
noncomputable section

def componentNorm (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair)
    (plus : Bool) : ℝ :=
  Real.sqrt (∑' k : ℤ, ENNReal.ofReal
    (w k ^ 2 *
      ‖NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ plus k‖ ^ 2)).toReal

end
end NlsGge.ThirdConsultation.M

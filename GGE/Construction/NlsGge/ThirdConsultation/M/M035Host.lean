import Mathlib
import NlsGge.ThirdConsultation.M.M033Host
import NlsGge.ThirdConsultation.M.M053Host

                                                                       
                                                                                                  
                                                                                                   
                                                                 
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.MEstimates
noncomputable section

open NlsGge.ThirdConsultation

/-- Source Lemma 13's explicit low polynomial; the final 2 is pair mass. -/
def forwardLowConstant (m : ℕ) (hm : 1 ≤ m) (u : M.SobolevR m) : ℝ :=
  (1 + 16 * Real.pi) ^ (2 * m) *
    (1 + MTwoMode.H1Norm (M.lowerSobolevCast 1 m hm u)) ^ (4 * m) *
    (2 * M.massCharge (M.physicalOfSobolev u))

end
end NlsGge.ThirdConsultation.MEstimates

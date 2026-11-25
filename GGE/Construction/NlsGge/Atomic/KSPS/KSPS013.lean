import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Host
import NlsGge.ThirdConsultation.KSPS.KSPS013Support

                                                                                                     
                                                                                                                 
                                                                                                    
                                                                                                  
                                                                                                               
                                           
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem integrated_riccati_vanishing
    (N k : ℕ) (φ : SobolevC N)
    (hk : 1 ≤ k ∧ k ≤ N + 1) :
    integralRiccatiLeft φ k = integralRiccatiRight φ k := by
  obtain ⟨hk1, hkN⟩ := hk
  unfold integralRiccatiRight
  by_cases h1 : k = 1
  · subst h1
    exact NlsGge.ThirdConsultation.KSPSWKB.rv_vanishing_one φ
  · exact NlsGge.ThirdConsultation.KSPSWKB.rv_vanishing_ge_two φ k (by omega) hkN

end
end NlsGge.ThirdConsultation.KSPS

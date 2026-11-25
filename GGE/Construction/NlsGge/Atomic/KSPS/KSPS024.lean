import Mathlib
import NlsGge.Atomic.KSPS.KSPS017
import NlsGge.Atomic.KSPS.KSPS019
import NlsGge.ThirdConsultation.KSPS.KSPS024Support

                                                                                                     
                                                                                                                      
                                                                                                                  
                                                                                                                      
                                                                                                   
                                                                                                                   
                                                                                                                      
                                                                                                               
                         
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem critical_spectral_expansion
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) :
  WeightedL2Error (N+1)
    (fun n => criticalEigenvalue φ n - spectralPolynomial φ n) := by
  obtain ⟨a, ha, hxi⟩ :=
    NlsGge.ThirdConsultation.KSPS024W.crit_localization_of rough_boundary_roots hN φ
  exact NlsGge.ThirdConsultation.KSPS024W.critical_spectral_expansion_of N hN φ a ha hxi
    (discriminant_derivative_WKB N hN φ (criticalEigenvalue φ) ⟨a, ha, hxi⟩)

end
end NlsGge.ThirdConsultation.KSPS

import Mathlib
import NlsGge.Atomic.KSPS.KSPS020
import NlsGge.Atomic.KSPS.KSPS024
import NlsGge.Atomic.KSPS.KSPS026
import NlsGge.Atomic.G1.G1054
import NlsGge.ThirdConsultation.KSPS.KSPS025Support

                                                                                                     
                                                                                                                           
                                                                
                                                                                                                    
                                                                                                                          
                                                                                                                  
                                                                                                                    
                                                                                                                    
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem midpoint_spectral_expansion
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) :
  WeightedL2Error (N+1)
    (fun n => midpoint φ n - spectralPolynomial φ n) :=
  NlsGge.ThirdConsultation.KSPS025W.midpoint_spectral_expansion_of N hN φ
    rough_periodic_endpoints (endpoint_quadratic_expansion N hN φ)
    NlsGge.Atomic.G1054S3.Final.G1054_main
    (critical_spectral_expansion N hN φ)

end
end NlsGge.ThirdConsultation.KSPS

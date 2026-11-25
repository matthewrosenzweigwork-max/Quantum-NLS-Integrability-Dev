import Mathlib
import NlsGge.Atomic.KSPS.KSPS011
import NlsGge.Atomic.KSPS.KSPS012
import NlsGge.Atomic.KSPS.KSPS013
import NlsGge.Atomic.KSPS.KSPS014
import NlsGge.Atomic.KSPS.KSPS015
import NlsGge.Atomic.KSPS.KSPS020
import NlsGge.ThirdConsultation.KSPS.KSPS026Support6

                                                                                                     
                                                                                                                      
                                                                                                               
                                                                                                                   
                                                                                                                   
                                                                                                                 
                                                                                                   
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem endpoint_quadratic_expansion
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) :
    EndpointQuadraticWKB N φ :=
  NlsGge.ThirdConsultation.KSPS026W.endpoint_quadratic_expansion_of N hN φ
    (fun xi hxi => WKB_endpoint_offdiagonal N hN φ xi hxi)
    (fun xi hxi => WKB_endpoint_diagonal N hN φ xi hxi)
    (fun k hk => integrated_riccati_vanishing N k φ hk)
    (fun lam hlam => (WKB_monodromy_entries N (sobolevNorm N φ) φ lam le_rfl hlam).2)
    (fun xi hxi => discriminant_WKB_sequence N hN φ xi hxi)
    rough_periodic_endpoints

end
end NlsGge.ThirdConsultation.KSPS

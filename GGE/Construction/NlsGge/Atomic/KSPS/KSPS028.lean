import Mathlib
import NlsGge.Atomic.KSPS.KSPS020
import NlsGge.Atomic.KSPS.KSPS025
import NlsGge.Atomic.KSPS.KSPS026
import NlsGge.ThirdConsultation.KSPS.KSPS028Support
import NlsGge.ThirdConsultation.KSPS.KSPS028Support2
import NlsGge.ThirdConsultation.M.M053Host

                                                                                                     
                                                                                                                       
                                                                                                                 
                                                                               
                                                                                                                      
                                                                                                                   
                                                                                                                 
                                                                                                                     
                                                                                                
set_option autoImplicit false
open NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem real_periodic_endpoint_expansion
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N)
    (hφ : NlsGge.ThirdConsultation.MRiccati.RealPair φ) :
  ∃ eplus eminus : ℤ → ℂ,
    LpSequence 4 eplus ∧ LpSequence 4 eminus ∧
    ∀ n : ℤ, n ≠ 0 →
      periodicPlus φ n =
        spectralPolynomial φ n +
          ‖physicalFourier (toPotPair φ).1 (-n)‖ +
          eplus n / indexValue n^(N+1) ∧
      periodicMinus φ n =
        spectralPolynomial φ n -
          ‖physicalFourier (toPotPair φ).1 (-n)‖ +
          eminus n / indexValue n^(N+1) :=
  NlsGge.ThirdConsultation.KSPS028W.real_periodic_endpoint_expansion_of N hN φ
    rough_periodic_endpoints (endpoint_quadratic_expansion N hN φ) (midpoint_spectral_expansion N hN φ)
    (NlsGge.ThirdConsultation.KSPS028Q.real_facts φ hφ).1 (NlsGge.ThirdConsultation.KSPS028Q.real_facts φ hφ).2

end
end NlsGge.ThirdConsultation.KSPS

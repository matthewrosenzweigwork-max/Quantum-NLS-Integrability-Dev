import Mathlib
import NlsGge.Atomic.M.M049

                                                                                                                      
                                                                                                                      
                                                                                                                    
                                                   
set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE

theorem actualBirkhoffTop38_inverse_polynomial
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ z : NlsGge.Sobolev38.SobolevCarrier38 (m : ℝ),
        ‖actualBirkhoffTop38.TinvC m z‖ ≤
          C * (1 + ‖z‖) ^ (4 * m - 2) :=
  actualBirkhoffTop38_inverse_polynomial_of m hm (NlsGge.ThirdConsultation.M.molnar_inverse_birkhoff m hm)

end NlsGge.ThirdConsultation.PDE

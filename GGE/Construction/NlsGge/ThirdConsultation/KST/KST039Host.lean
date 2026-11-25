import Mathlib
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST027
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST034Host

                                                                                                                    
                                                                                                       
                                                                                         
                                                                                                                   
                                                                                                           
                                                                                              
                               
                                                                                                     
                                                   
set_option autoImplicit false
noncomputable section
open NlsGge.GK38 NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

def adaptedInverse (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (M : ℝ) (N : ℕ) (y : Weighted ω) : Weighted ω :=
  if h : ∃ x ∈ componentBall ω M, adaptedFourier ω hω N x = y
  then Classical.choose h else 0

end NlsGge.ThirdConsultation.KST
end

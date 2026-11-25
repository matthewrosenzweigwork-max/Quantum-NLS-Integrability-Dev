import Mathlib
import NlsGge.Atomic.M.M001

                                                                                                                      
                                                                                                                                
                                                                                                                                         
set_option autoImplicit false
open Set Filter MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M
noncomputable section

/-- Complex level-k action J_{n,k}; raw GK higherAction has the extra k. -/
def complexHigherAction (φ : PotPair) (n : ℤ) (k : ℕ) : ℂ :=
  if hk : 1 ≤ k then
    (k : ℂ)⁻¹ * NlsGge.GKDefinitionDesign.higherAction k φ n
  else 0

end
end NlsGge.ThirdConsultation.M

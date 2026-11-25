import Mathlib
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.DM.DM004

                                                                                                                          
                                                                                                       
                                                                                                                 
                                                                                                           
                                                                         
                                                                                                     
                                  
set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

def diagonalZero (n : ℤ) (φ : Potential) : ℂ :=
  if h : ∃ z : ℂ, z ∈ Metric.closedBall (center n) (Real.pi/48) ∧
      z = center n + a φ n z then Classical.choose h else center n

end NlsGge.ThirdConsultation.KST
end

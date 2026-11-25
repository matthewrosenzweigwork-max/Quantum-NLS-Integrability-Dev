import Mathlib
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST019

                                                                                                                          
                                                                                                               
                                                                                                            
                                                                                                                      
                                                                                    
set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.KST

def Balanced (n : ℤ) (a b c : ℂ → ℂ) (σ : ℂ) : Prop :=
  SmallCoefficients n a b c ∧ σ = center n + a σ ∧
  ‖σ - center n‖ ≤ Real.pi / 48 ∧ b σ * c σ ≠ 0 ∧
  (1 / 9 : ℝ) ≤ ‖c σ / b σ‖ ∧ ‖c σ / b σ‖ ≤ 9

def rootRadius (b c : ℂ → ℂ) (σ : ℂ) : ℝ := Real.sqrt ‖b σ * c σ‖

end NlsGge.ThirdConsultation.KST
end

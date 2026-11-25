import Mathlib

                                                                                                  
                                                                                                   
                                                                                          
                                                                                                             
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M
noncomputable section

def actionMomentRelations (m : ℕ) (A0 A1 Am : ℝ) : Prop :=
  0 ≤ A0 ∧ A0 ≤ A1 ∧ A1 ≤ Am ∧
  A1^m ≤ Am*A0^(m-1)

def ActionMomentRelations := actionMomentRelations

end
end NlsGge.ThirdConsultation.M

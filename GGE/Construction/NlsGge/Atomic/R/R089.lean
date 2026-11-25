import NlsGge.Composition.TrigApprox

                                                                                                             
                                                                                                                          
                                                                                        
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.R
noncomputable section
open NlsGge.Composition

theorem r089_exists_truncate_near {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] {ε : ℝ} (g : Model X) (hε : 0 < ε) :
    ∃ S : Finset ℤ, ‖g - truncate S g‖ < ε :=
  NlsGge.Composition.exists_truncate_near g hε

end
end NlsGge.ThirdConsultation.R

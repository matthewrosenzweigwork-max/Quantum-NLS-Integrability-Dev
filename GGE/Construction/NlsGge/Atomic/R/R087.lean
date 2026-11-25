                                                                                                           
                                                                                                                                       
                                                                                                                          
                                                                                                                             
                                                                                              
import Mathlib
import NlsGge.Composition.Multilinear

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.R
noncomputable section

theorem r087_norm_multCLM_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y] {w : ℤ → ℝ}
    (hw : NlsGge.Composition.AdmissibleWeight w) (k : ℕ) :
    ‖NlsGge.Composition.multCLM hw k (X := X) (Y := Y)‖ ≤ (NlsGge.Composition.prodConst hw) ^ k :=
  NlsGge.Composition.norm_multCLM_le hw k

end
end NlsGge.ThirdConsultation.R

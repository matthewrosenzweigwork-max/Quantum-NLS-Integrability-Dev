import Mathlib
import NlsGge.Composition.Model

                                                                                                                                                                                                                                                                                  
                                                                                                                                                 
                                                                                                                               
                                                                                                                   

set_option autoImplicit false

namespace NlsGge.Atomic.R083

theorem norm_synth_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {w : ℤ → ℝ} (hw : NlsGge.Composition.AdmissibleWeight w) (g : NlsGge.Composition.Model X)
    (θ : AddCircle (1 : ℝ)) :
    ‖NlsGge.Composition.synth w g θ‖ ≤ NlsGge.Composition.supConst w * ‖g‖ :=
  NlsGge.Composition.norm_synth_le hw g θ

end NlsGge.Atomic.R083

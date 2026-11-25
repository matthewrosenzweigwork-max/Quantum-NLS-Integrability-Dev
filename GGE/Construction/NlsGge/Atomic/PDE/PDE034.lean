                                                                                                      
                                                                                                                    
                                                       
import Mathlib
import NlsGge.Atomic.PDE.PDE029
import NlsGge.NLS38.GlobalH1_38

set_option autoImplicit false
open NlsGge.NLS38 NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem h1_global_unique (x : ℤ → ℂ) (hx : x ∈ h1) :
    ∃! u, IsNLSSol u ∧ u 0 = x := by
  obtain ⟨u, hu, h0⟩ := nls_exists x hx
  refine ⟨u, ⟨hu, h0⟩, fun w hw => ?_⟩
  exact nls_unique hw.1 hu (hw.2.trans h0.symm)

end
end NlsGge.ThirdConsultation.PDE

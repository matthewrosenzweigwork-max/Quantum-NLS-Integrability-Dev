                                                                                                                 
                                                                                                                                                                                  
                                                                                                                                                 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         
import Mathlib
import NlsGge.NLS38.GlobalH1_38

set_option autoImplicit false
open NlsGge.NLS38 NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

abbrev h1 : Set (ℤ → ℂ) := seqSobolev38 ((1 : ℕ) : ℝ)

theorem h1_le_coercive_energy (x : ℤ → ℂ) (hx : x ∈ h1) :
    hn 1 x ≤ Real.sqrt (mass x + ham x / (4 * Real.pi ^ 2)) :=
  hn_le_Bx38 hx

end
end NlsGge.ThirdConsultation.PDE

import Mathlib
import NlsGge.Hierarchy.ALC12Exact38

                                                                                                                                            
                                                                                                                                                                                                                                                                                                               
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Set Filter Topology MeasureTheory
open NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.AL

theorem al014 {L : ℕ} [NeZero L] (hL : 3 ≤ L)
    (α : ZMod L → ℂ) (hα : IsALField38 α) :
  alC38 α 1 = ∑ j : ZMod L, α j*star (α (j-1)) ∧
  alC38 α 2 =
    (∑ j : ZMod L, α j*star (α (j-2))*(1-((‖α (j-1)‖^2 : ℝ) : ℂ))) -
    (1/2 : ℂ) * ∑ j : ZMod L, (α j*star (α (j-1)))^2 :=
  ⟨alC38_one38 hL hα, alC38_two38 hL hα⟩

end NlsGge.ThirdConsultation.AL

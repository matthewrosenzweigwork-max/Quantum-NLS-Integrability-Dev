import Mathlib
import NlsGge.Hierarchy.ALMoments38

                                                                                                                                            
                                                                                                                                                                                                 
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Set Filter Topology MeasureTheory
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.AL

theorem al026 {L : ℕ} [NeZero L] (hL : 3 ≤ L)
    (α : ZMod L → ℂ) (hα : IsALField38 α) :
  (∀ j : ℕ, 0 ≤ alK38 α j) ∧
  alK38 α 0 = alMass38 L α ∧
  alK38 α 1 = 2*alMass38 L α-2*(alC38 α 1).re ∧
  alK38 α 1 = alHd α ∧
  alK38 α 2 = 6*alMass38 L α-8*(alC38 α 1).re+2*(alC38 α 2).re ∧
  alK38 α 2 = alKd α :=
  ⟨alK38_nonneg hα, alK38_zero α, alK38_one α, alK38_one_eq_alHd hL hα,
    alK38_two α, alK38_two_eq_alKd hL hα⟩

end NlsGge.ThirdConsultation.AL

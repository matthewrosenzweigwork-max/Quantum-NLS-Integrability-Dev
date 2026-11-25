import Mathlib
import NlsGge.Hierarchy.ALPositiveDecompositions38

                                                                                                                                            
                                                                                                                                                           
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Set Filter Topology MeasureTheory
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.AL

theorem al047 (L : ℕ) [NeZero L] (α : ZMod L → ℂ) :
    alMd α = (∑ j, alR α j) + ∑ j, alEll (alR α j) ∧
    alHd α = (∑ j, ‖α j - α (j - 1)‖ ^ 2) +
      2 * ∑ j, alEll (alR α j) :=
  ⟨alMd_split α, alHd_split α⟩

end NlsGge.ThirdConsultation.AL

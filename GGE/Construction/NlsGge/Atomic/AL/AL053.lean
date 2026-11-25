import Mathlib
import NlsGge.Atomic.AL.AL065
import NlsGge.Hierarchy.ALPositiveDecompositions38

                                                                        
                                                                                             
                                                                                        
                                                                                                    
                                                                                                                 
                                                                                                       
                                                                                                        
                                                                                                            
                                                                    
set_option autoImplicit false

open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.AL

theorem al053 (L : ℕ) [NeZero L] (α : ZMod L → ℂ)
    (hα : ∀ j, ‖α j‖ < 1) :
    alKd α =
      (∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2) +
      ((3 : ℝ) / 2) * (∑ j, (alR α (j + 1) - alR α j) ^ 2) +
      (∑ j, alR α j * ‖α (j + 1) - α (j - 1)‖ ^ 2) +
      2 * (∑ j, (α j * star (α (j - 1))).im ^ 2) +
      6 * (∑ j, logRemainder2 (alR α j)) ∧
    (∀ j, 0 ≤ logRemainder2 (alR α j)) ∧
    0 ≤ (∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2) ∧
    0 ≤ ((3 : ℝ) / 2) * (∑ j, (alR α (j + 1) - alR α j) ^ 2) ∧
    0 ≤ (∑ j, alR α j * ‖α (j + 1) - α (j - 1)‖ ^ 2) ∧
    0 ≤ 2 * (∑ j, (α j * star (α (j - 1))).im ^ 2) ∧
    0 ≤ 6 * (∑ j, logRemainder2 (alR α j)) ∧
    0 ≤ alKd α := by
  have hK := alKd_squares α
  have hlog : ∀ j : ZMod L, logRemainder2 (alR α j) =
      -Real.log (1 - alR α j) - alR α j - (1 / 2) * alR α j ^ 2 := by
    intro j
    unfold logRemainder2 alEll
    ring
  have hr0 : ∀ j : ZMod L, 0 ≤ alR α j := fun j => by
    unfold alR; positivity
  have hl0 : ∀ j : ZMod L, 0 ≤ logRemainder2 (alR α j) := fun j => by
    rw [hlog]
    exact alEll_sq_nonneg (hr0 j) (alR_lt_one α hα j)
  have hsum : ∑ j, logRemainder2 (alR α j) =
      ∑ j, (-Real.log (1 - alR α j) - alR α j - (1 / 2) * alR α j ^ 2) :=
    Finset.sum_congr rfl fun j _ => hlog j
  refine ⟨?_, fun j => hl0 j, ?_, ?_, ?_, ?_, ?_, alKd_nonneg α hα⟩
  · rw [hK, hsum]
    rfl
  · exact Finset.sum_nonneg fun j _ => by positivity
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (hr0 j) (by positivity)
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => hl0 j)

end NlsGge.ThirdConsultation.AL

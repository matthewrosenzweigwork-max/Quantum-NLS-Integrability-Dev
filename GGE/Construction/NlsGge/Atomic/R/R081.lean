import Mathlib
import NlsGge.Composition.Weight

                                                                                                          
                                                                                                                       
                                                                             

set_option autoImplicit false
open NlsGge.Composition

namespace NlsGge.Atomic.R081

theorem R081_main : ((
  ∀ (a : ℝ), 0 < a → ∀ (b : ℝ),
    Summable (fun n : ℤ => (srcWeight a b n)⁻¹ ^ 2) ∧
    (∀ η : ℝ, 0 < η → Summable (fun n : ℤ => srcWeight a b n ^ 2 * Real.exp (-η * |(n : ℝ)|))) ∧
    (∀ n : ℤ, 0 < srcWeight a b n) ∧
    (∀ n : ℤ, srcWeight a b (-n) = srcWeight a b n)
  : Prop)) := by
  intro a ha b
  refine ⟨summable_srcWeight_inv_sq ha b, fun η hη => summable_srcWeight_sq_mul_exp a b hη,
    fun n => srcWeight_pos a b n, fun n => ?_⟩
  simp only [srcWeight, jbr, Int.cast_neg, abs_neg, neg_sq]

end NlsGge.Atomic.R081

import Mathlib

namespace NlsGge.Atomic.S007


                                                                                                                                          
set_option autoImplicit false


theorem S007_main : ((Summable (fun r : ℤ => if r = 0 then (0 : ℝ) else 1 / ((r : ℝ) ^ 2 * ((-r : ℤ) : ℝ) ^ 2)) ∧
    (∑' r : ℤ, (if r = 0 then (0 : ℝ) else 1 / ((r : ℝ) ^ 2 * ((-r : ℤ) : ℝ) ^ 2))) =
      ∑' r : ℤ, (if r = 0 then (0 : ℝ) else ((r : ℝ) ^ 4)⁻¹) ∧
    ∃ C : ℝ, (∑' r : ℤ, (if r = 0 then (0 : ℝ) else 1 / ((r : ℝ) ^ 2 * ((-r : ℤ) : ℝ) ^ 2))) ≤ C) : Prop) := by
  have hf : (fun r : ℤ => if r = 0 then (0 : ℝ) else 1 / ((r : ℝ) ^ 2 * ((-r : ℤ) : ℝ) ^ 2)) =
      fun r : ℤ => 1 / (r : ℝ) ^ 4 := by
    funext r
    split_ifs with h0
    · simp [h0]
    · push_cast
      ring
  have hf2 : (fun r : ℤ => if r = 0 then (0 : ℝ) else ((r : ℝ) ^ 4)⁻¹) =
      fun r : ℤ => 1 / (r : ℝ) ^ 4 := by
    funext r
    split_ifs with h0
    · simp [h0]
    · simp
  have hs : Summable (fun r : ℤ => 1 / (r : ℝ) ^ 4) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [hf]; exact hs
  · rw [hf, hf2]
  · exact ⟨_, le_rfl⟩


end NlsGge.Atomic.S007

import Mathlib

                                                                                           
                                                                    
                                                                                                    
                                                                                            

set_option autoImplicit false

namespace NlsGge.Atomic.AL.AL083

theorem AL083_helper : ((
  (∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    |2 * Real.cos (Real.pi * (((2 * (N : ℝ) + 1)⁻¹)) / 2) / ((2 * (N : ℝ) + 1)⁻¹) - 4 * (N : ℝ)| ≤ C) ∧
  (∀ N : ℕ, (2 * Real.pi * (N : ℝ)) = 2 * Real.pi * (N : ℝ))
  : Prop)) := by
  refine ⟨⟨2, fun N hN => ?_⟩, fun N => rfl⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmpos : (0 : ℝ) < 2 * (N : ℝ) + 1 := by linarith
  have hθ : Real.pi * ((2 * (N : ℝ) + 1)⁻¹) / 2 = Real.pi / (2 * (2 * (N : ℝ) + 1)) := by
    field_simp
  rw [hθ]
  have hval : 2 * Real.cos (Real.pi / (2 * (2 * (N : ℝ) + 1))) / ((2 * (N : ℝ) + 1)⁻¹) -
      4 * (N : ℝ) = 2 - 2 * (2 * (N : ℝ) + 1) * (1 - Real.cos (Real.pi / (2 * (2 * (N : ℝ) + 1)))) := by
    field_simp
    ring
  rw [hval]
  have hcos : 1 - (Real.pi / (2 * (2 * (N : ℝ) + 1))) ^ 2 / 2 ≤ Real.cos (Real.pi / (2 * (2 * (N : ℝ) + 1))) :=
    Real.one_sub_sq_div_two_le_cos
  have hc1 : Real.cos (Real.pi / (2 * (2 * (N : ℝ) + 1))) ≤ 1 := Real.cos_le_one _
  have hx2 : (2 * (N : ℝ) + 1) * (Real.pi / (2 * (2 * (N : ℝ) + 1))) ^ 2 = Real.pi ^ 2 / (4 * (2 * (N : ℝ) + 1)) := by
    field_simp
    ring
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hsmall : Real.pi ^ 2 / (4 * (2 * (N : ℝ) + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hbound : 2 * (2 * (N : ℝ) + 1) * (1 - Real.cos (Real.pi / (2 * (2 * (N : ℝ) + 1)))) ≤ 1 := by
    nlinarith
  have hnonneg : 0 ≤ 2 * (2 * (N : ℝ) + 1) * (1 - Real.cos (Real.pi / (2 * (2 * (N : ℝ) + 1)))) := by
    apply mul_nonneg (by positivity)
    linarith
  rw [abs_le]
  constructor <;> linarith

end NlsGge.Atomic.AL.AL083

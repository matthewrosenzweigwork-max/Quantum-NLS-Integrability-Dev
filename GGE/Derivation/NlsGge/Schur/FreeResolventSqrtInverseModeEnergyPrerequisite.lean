import NlsGge.Schur.FreeResolventPotentialColumnRowOperatorBoundsAfterScalarNormPrerequisite

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- Scalar conversion from a squared resonant energy bound to its exact
inverse-mode square-root bound. -/
theorem freeResolvent_sqrt_inverse_mode_energy_le_prerequisite
    (n : ℤ) (hn : n ≠ 0) (R a : ℝ)
    (hR : 0 ≤ R) (ha : 0 ≤ a) (hab : a ≤ R) :
    Real.sqrt ((2 / (n : ℝ) ^ 2) * a ^ 2) ≤
      Real.sqrt 2 * R / |(n : ℝ)| := by
  have hn0 : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hden : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero hn0
  have hsq : a ^ 2 ≤ R ^ 2 := (sq_le_sq₀ ha hR).2 hab
  have htarget :
      (Real.sqrt 2 * R / |(n : ℝ)|) ^ 2 = (2 / (n : ℝ) ^ 2) * R ^ 2 := by
    rw [div_pow, sq_abs, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hinner : (2 / (n : ℝ) ^ 2) * a ^ 2 ≤
      (Real.sqrt 2 * R / |(n : ℝ)|) ^ 2 := by
    rw [htarget]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  calc
    Real.sqrt ((2 / (n : ℝ) ^ 2) * a ^ 2) ≤
        Real.sqrt ((Real.sqrt 2 * R / |(n : ℝ)|) ^ 2) := Real.sqrt_le_sqrt hinner
    _ = Real.sqrt 2 * R / |(n : ℝ)| := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      positivity

end NlsGge.Schur

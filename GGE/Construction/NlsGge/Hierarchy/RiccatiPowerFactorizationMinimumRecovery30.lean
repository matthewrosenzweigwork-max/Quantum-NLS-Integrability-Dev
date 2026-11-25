import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

/-- The scalar power factor needed to rewrite the coefficient estimate in
terms of the square of the multiplier norm. -/
theorem real_two_pi_power_factorizationMinimumRecovery30 (k : ℕ) :
    ((2 : ℝ) ^ k) ^ 2 * (Real.pi ^ k) ^ 2 = (2 * Real.pi) ^ (2 * k) := by
  calc
    ((2 : ℝ) ^ k) ^ 2 * (Real.pi ^ k) ^ 2 =
        ((2 : ℝ) ^ k * Real.pi ^ k) ^ 2 := by rw [← mul_pow]
    _ = ((2 * Real.pi) ^ k) ^ 2 := by rw [← mul_pow]
    _ = (2 * Real.pi) ^ (2 * k) := by
      rw [← pow_mul]
      congr 1
      omega

end NlsGge.HierarchyRiccati.Core

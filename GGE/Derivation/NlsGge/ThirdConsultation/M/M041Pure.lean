import Mathlib

/- M-041 PURE CORE (proof development, AUTHOR; not reviewed). Intended target NlsGge/ThirdConsultation/M/M041Pure.lean,
   namespace NlsGge.ThirdConsultation.M041B. Mathlib only. -/
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace NlsGge.ThirdConsultation.M041B
noncomputable section

/-- 4·(2/π)∫ x²f = (2/π)∫ (2x)²f, written with the exponents produced at k = 3 / k = 1. -/
theorem four_moment (f : ℝ → ℝ) (a b : ℝ) :
    (4 : ℝ) ^ 1 * ((2 / Real.pi) * ∫ x in a..b, x ^ (2 * 1 + 1 - 1) * f x) =
      (2 / Real.pi) * ∫ x in a..b, (2 * x) ^ (2 * 1) * f x := by
  have e : (∫ x in a..b, (2 * x) ^ (2 * 1) * f x) = 4 * ∫ x in a..b, x ^ (2 * 1 + 1 - 1) * f x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    rw [show (2 * 1 + 1 - 1 : ℕ) = 2 from rfl, show (2 * 1 : ℕ) = 2 from rfl]
    ring
  rw [e]
  ring

/-- A summable nonnegative sequence has a finite ENNReal sum. -/
theorem ennreal_tsum_ne_top {f : ℤ → ℝ} (hf : ∀ n, 0 ≤ f n) (hs : Summable f) :
    (∑' n : ℤ, ENNReal.ofReal (f n)) ≠ ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hs]
  exact ENNReal.ofReal_ne_top

/-- The final inequality step: S − c·I ≤ S for c, I ≥ 0. -/
theorem sub_nonneg_mul_le (S c I : ℝ) (hc : 0 ≤ c) (hI : 0 ≤ I) : S - c * I ≤ S := by
  nlinarith [mul_nonneg hc hI]

end
end NlsGge.ThirdConsultation.M041B

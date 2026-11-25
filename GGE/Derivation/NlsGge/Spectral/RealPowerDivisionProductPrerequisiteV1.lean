import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

/-- Normalize the scalar majorant's factorial denominator before combining
powers with `mul_pow`. -/
theorem real_pow_div_mul_pow (a b d : ℝ) (n : ℕ) :
    (a ^ n / d) * b ^ n = (a * b) ^ n / d := by
  rw [div_mul_eq_mul_div, ← mul_pow]

end NlsGge.SpectralFoundations

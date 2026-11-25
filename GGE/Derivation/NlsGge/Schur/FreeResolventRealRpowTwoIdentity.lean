import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace NlsGge.Schur

/-- The pinned real exponent `2` agrees with the natural square, including for
negative inputs. -/
theorem real_rpow_two_eq_pow (x : ℝ) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
  exact Real.rpow_natCast x 2

end NlsGge.Schur

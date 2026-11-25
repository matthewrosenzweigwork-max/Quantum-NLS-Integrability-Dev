import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace NlsGge.Schur

/-- Exact complex norm identity for the scalar coefficient squares used in
Fourier-energy sums. -/
theorem complex_norm_mul_sq_prerequisite (a b : ℂ) :
    ‖a * b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  rw [norm_mul, mul_pow]

end NlsGge.Schur

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open scoped ComplexConjugate

namespace NlsGge.Hierarchy

/-- The real part of the actual complex star-product is the squared norm.
This tiny prerequisite isolates the pinned conjugation notation used in the
finite Q₂ source bridge. -/
theorem complex_re_mul_star_eq_norm_sq_prerequisite (z : ℂ) :
    Complex.re (z * star z) = ‖z‖ ^ 2 := by
  have hstar : star z = conj z := congrFun (RCLike.star_def (K := ℂ)) z
  have hprod : z * conj z = Complex.ofReal (‖z‖ ^ 2) := by
    simpa only [← Complex.ofReal_pow] using (Complex.mul_conj' z)
  calc
    Complex.re (z * star z) = Complex.re (z * conj z) := by rw [hstar]
    _ = Complex.re (Complex.ofReal (‖z‖ ^ 2)) := congrArg Complex.re hprod
    _ = ‖z‖ ^ 2 := by rw [Complex.ofReal_re]

end NlsGge.Hierarchy

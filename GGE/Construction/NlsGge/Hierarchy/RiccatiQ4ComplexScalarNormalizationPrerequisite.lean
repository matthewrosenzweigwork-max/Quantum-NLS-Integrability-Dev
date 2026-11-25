import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati

open scoped ComplexConjugate

/-- Real casts remain real after taking a natural power and then the real part. -/
theorem q4RealCastPowRealPart (r : ℝ) (n : ℕ) :
    Complex.re ((r : ℂ) ^ n) = r ^ n := by
  rw [← Complex.ofReal_pow]
  exact Complex.ofReal_re _

/-- The real part of a product of real casts is the corresponding real product. -/
theorem q4RealCastMulRealPart (r s : ℝ) :
    Complex.re ((r : ℂ) * (s : ℂ)) = r * s := by
  rw [← Complex.ofReal_mul]
  exact Complex.ofReal_re _

/-- Complex conjugation preserves natural powers, in the pinned `star` notation. -/
theorem q4StarPow (z : ℂ) (n : ℕ) : star (z ^ n) = (star z) ^ n :=
  star_pow z n

end NlsGge.HierarchyRiccati

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati

open scoped ComplexConjugate

/-- The real part of a complex number plus its conjugate is twice its real part. -/
theorem q4ConjugateRealPartAddition (z : ℂ) :
    Complex.re (z + star z) = 2 * Complex.re z := by
  simp only [Complex.add_re, RCLike.star_def, Complex.conj_re]
  ring

end NlsGge.HierarchyRiccati

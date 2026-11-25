import NlsGge.Hierarchy.RiccatiHomogeneousComponentProductExpansionThird
import NlsGge.Hierarchy.RiccatiHomogeneousComponentSuccessorMulGeneratorThird
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open MvPolynomial

/-- Multiplication by a source generator has zero degree-zero projection. -/
theorem homogeneousComponent_zero_mul_X (v : Jet) (P : Poly) :
    MvPolynomial.homogeneousComponent 0 (MvPolynomial.X v * P) = 0 := by
  rw [MvPolynomial.homogeneousComponent_zero]
  have hcoeff : (MvPolynomial.X v * P).coeff 0 = 0 := by
    classical
    rw [MvPolynomial.coeff_mul]
    simp
  rw [hcoeff]
  simp

/-- The degree-one projection of a generator times a polynomial is the
generator times the degree-zero projection of that polynomial. -/
theorem homogeneousComponent_one_mul_X (v : Jet) (P : Poly) :
    MvPolynomial.homogeneousComponent 1 (MvPolynomial.X v * P) =
      MvPolynomial.X v * MvPolynomial.homogeneousComponent 0 P := by
  simpa using homogeneousComponent_succ_mul_X 0 v P

end NlsGge.HierarchyRiccati.Core

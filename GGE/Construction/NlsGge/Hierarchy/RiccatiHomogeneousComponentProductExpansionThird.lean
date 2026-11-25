import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open MvPolynomial

/-- The degree-d homogeneous component of a product is the sum of the
products of homogeneous components whose degrees add to d. The ranges are
bounded by the actual total degrees of the two source polynomials. -/
theorem homogeneousComponent_mul_expanded (d : ℕ) (P Q : Poly) :
    MvPolynomial.homogeneousComponent d (P * Q) =
      ∑ a ∈ Finset.range (P.totalDegree + 1),
        ∑ b ∈ Finset.range (Q.totalDegree + 1),
          (if d = a + b then
            MvPolynomial.homogeneousComponent a P *
              MvPolynomial.homogeneousComponent b Q
          else 0) := by
  classical
  conv_lhs =>
    rw [← MvPolynomial.sum_homogeneousComponent P,
      ← MvPolynomial.sum_homogeneousComponent Q]
  rw [Finset.sum_mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [MvPolynomial.homogeneousComponent_of_mem
    ((MvPolynomial.homogeneousComponent_isHomogeneous a P).mul
      (MvPolynomial.homogeneousComponent_isHomogeneous b Q))]

end NlsGge.HierarchyRiccati.Core

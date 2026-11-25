import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open MvPolynomial

/-- Multiplication by one actual jet generator shifts ordinary homogeneous
degree by exactly one. -/
theorem homogeneousComponent_succ_mul_X (d : ℕ) (v : Jet) (P : Poly) :
    MvPolynomial.homogeneousComponent (d + 1) (MvPolynomial.X v * P) =
      MvPolynomial.X v * MvPolynomial.homogeneousComponent d P := by
  induction P using MvPolynomial.induction_on' with
  | monomial s r =>
      conv_lhs =>
        rw [show (MvPolynomial.X v : Poly) = MvPolynomial.X v ^ (1 : ℕ) by simp]
      rw [← MvPolynomial.monomial_single_add]
      have hs : (Finsupp.single v 1 + s).degree = s.degree + 1 := by
        rw [Finsupp.degree.map_add]
        simp
        omega
      rw [MvPolynomial.homogeneousComponent_of_mem
        (MvPolynomial.isHomogeneous_monomial r hs),
        MvPolynomial.homogeneousComponent_of_mem
          (MvPolynomial.isHomogeneous_monomial r rfl)]
      by_cases h : d = s.degree
      · subst d
        simp [hs]
        simpa only [pow_one] using
          (MvPolynomial.monomial_single_add (n := v) (e := 1) (s := s) (a := r))
      · have h' : d + 1 ≠ s.degree + 1 := by omega
        simp [h, h', hs]
  | add P Q hP hQ =>
      simp only [mul_add, map_add, hP, hQ]

end NlsGge.HierarchyRiccati.Core

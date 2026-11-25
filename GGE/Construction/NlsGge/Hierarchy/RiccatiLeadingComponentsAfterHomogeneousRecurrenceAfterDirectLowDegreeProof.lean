import NlsGge.Hierarchy.RiccatiHomogeneousRecurrenceAfterProjectionCommutationSecond
import NlsGge.Hierarchy.RiccatiHomogeneousComponentMulGeneratorLowDegreesAfterProductAndShiftSecond
import NlsGge.Hierarchy.RiccatiHomogeneousComponentProductExpansionThird
import NlsGge.Hierarchy.RiccatiLowOrderAlgebraAfterCore
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open MvPolynomial

/-- Degree zero of a product is the product of the two degree-zero parts. -/
theorem homogeneousComponent_zero_mul (P Q : Poly) :
    MvPolynomial.homogeneousComponent 0 (P * Q) =
      MvPolynomial.homogeneousComponent 0 P * MvPolynomial.homogeneousComponent 0 Q := by
  rw [MvPolynomial.homogeneousComponent_zero, MvPolynomial.homogeneousComponent_zero,
    MvPolynomial.homogeneousComponent_zero]
  have hcoeff : (P * Q).coeff 0 = P.coeff 0 * Q.coeff 0 := by
    classical
    rw [MvPolynomial.coeff_mul]
    simp
  rw [hcoeff]
  simp

/-- Every actual source Riccati polynomial has zero constant component. -/
theorem p_zero_homogeneous_component (n : ℕ) :
    MvPolynomial.homogeneousComponent 0 (p n) = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [p]
  | one =>
      rw [p_one]
      have hX : (MvPolynomial.X (true, 0) : Poly).IsHomogeneous 1 :=
        MvPolynomial.isHomogeneous_X _ _
      rw [MvPolynomial.homogeneousComponent_of_mem hX.neg]
      simp
  | more n ihn ihn1 =>
      rw [p_homogeneous_recurrence n 0, ihn1]
      simp only [map_zero, zero_add]
      apply Finset.sum_eq_zero
      intro l hl
      exact homogeneousComponent_zero_mul_X _ _

/-- The degree-one component of the actual source sequence is its unique
linear Riccati term. This statement is only about ordinary field degree. -/
theorem p_linear_homogeneous_component (n : ℕ) (hn : 1 ≤ n) :
    MvPolynomial.homogeneousComponent 1 (p n) =
      -MvPolynomial.X (true, n - 1) := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one =>
      rw [p_one]
      have hX : (MvPolynomial.X (true, 0) : Poly).IsHomogeneous 1 :=
        MvPolynomial.isHomogeneous_X _ _
      rw [MvPolynomial.homogeneousComponent_of_mem hX.neg]
      simp
  | more n ihn ihn1 =>
      have hn1 : 1 ≤ n + 1 := by omega
      rw [p_homogeneous_recurrence n 1, ihn1 hn1]
      rw [spatialD.map_neg, spatialD_jet]
      have hsum :
          (∑ l ∈ (Finset.Icc 1 n).attach,
            MvPolynomial.homogeneousComponent 1
              (MvPolynomial.X (false, 0) * (p (n + 1 - l.1) * p l.1))) = 0 := by
        apply Finset.sum_eq_zero
        intro l hl
        rw [homogeneousComponent_one_mul_X, homogeneousComponent_zero_mul,
          p_zero_homogeneous_component (n + 1 - l.1),
          p_zero_homogeneous_component l.1]
        simp
      rw [hsum]
      simp

end NlsGge.HierarchyRiccati.Core

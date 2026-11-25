import NlsGge.Hierarchy.RiccatiLowOrderAlgebraAfterCore
import NlsGge.Hierarchy.RiccatiPolynomialEvaluationAPI
import NlsGge.Hierarchy.RiccatiAttachedIccSmallSumPrerequisite
import NlsGge.Hierarchy.RiccatiSpatialDerivationNatCastCoefficientPrerequisite
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open scoped ComplexConjugate Interval

theorem p_four_after_natCast_prerequisite :
    p 4 = -MvPolynomial.X (true, 3) +
      MvPolynomial.X (false, 1) *
        (MvPolynomial.X (true, 0) * MvPolynomial.X (true, 0)) +
      4 * MvPolynomial.X (false, 0) * MvPolynomial.X (true, 0) *
        MvPolynomial.X (true, 1) := by
  rw [p_recurrence 2]
  rw [attachedIcc12_sum_nat (f := fun l : ℕ => p (3 - l) * p l)]
  simp only [Nat.reduceSub]
  rw [p_three, p_two, p_one]
  simp only [spatialD.map_add, spatialD.map_neg, spatialD.map_smul,
    spatialD.leibniz, spatialD_jet]
  ring

theorem p_five_after_natCast_prerequisite :
    p 5 = -MvPolynomial.X (true, 4) +
      MvPolynomial.X (false, 2) *
        (MvPolynomial.X (true, 0) * MvPolynomial.X (true, 0)) +
      6 * MvPolynomial.X (false, 1) * MvPolynomial.X (true, 0) *
        MvPolynomial.X (true, 1) +
      5 * MvPolynomial.X (false, 0) *
        (MvPolynomial.X (true, 1) * MvPolynomial.X (true, 1)) +
      6 * MvPolynomial.X (false, 0) * MvPolynomial.X (true, 0) *
        MvPolynomial.X (true, 2) -
      2 * MvPolynomial.X (false, 0) * MvPolynomial.X (false, 0) *
        (MvPolynomial.X (true, 0) * MvPolynomial.X (true, 0) *
          MvPolynomial.X (true, 0)) := by
  rw [p_recurrence 3]
  rw [attachedIcc13_sum_nat (f := fun l : ℕ => p (4 - l) * p l)]
  simp only [Nat.reduceSub]
  rw [p_four_after_natCast_prerequisite, p_three, p_two, p_one]
  simp only [spatialD.map_add, spatialD.map_neg, spatialD.map_smul,
    spatialD.leibniz, spatialD_four_eq_zero, spatialD_jet]
  ring

theorem formalQ4Density_formula_after_natCast_prerequisite :
    formalChargeIntegrand 2 =
      MvPolynomial.X (false, 0) * MvPolynomial.X (true, 4) -
      MvPolynomial.X (false, 0) * MvPolynomial.X (false, 2) *
        (MvPolynomial.X (true, 0) * MvPolynomial.X (true, 0)) -
      6 * MvPolynomial.X (false, 0) * MvPolynomial.X (false, 1) *
        MvPolynomial.X (true, 0) * MvPolynomial.X (true, 1) -
      5 * MvPolynomial.X (false, 0) * MvPolynomial.X (false, 0) *
        (MvPolynomial.X (true, 1) * MvPolynomial.X (true, 1)) -
      6 * MvPolynomial.X (false, 0) * MvPolynomial.X (false, 0) *
        MvPolynomial.X (true, 0) * MvPolynomial.X (true, 2) +
      2 * MvPolynomial.X (false, 0) * MvPolynomial.X (false, 0) *
        MvPolynomial.X (false, 0) *
        (MvPolynomial.X (true, 0) * MvPolynomial.X (true, 0) *
          MvPolynomial.X (true, 0)) := by
  unfold formalChargeIntegrand
  rw [p_five_after_natCast_prerequisite]
  norm_num
  ring

end NlsGge.HierarchyRiccati.Core

end

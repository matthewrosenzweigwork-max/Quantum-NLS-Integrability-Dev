import NlsGge.Hierarchy.RiccatiMonomialPeriodicIBPStepRecoveryThird
import NlsGge.Hierarchy.RiccatiJetEvaluationFiniteIntervalSumRecoverySecond
import NlsGge.Hierarchy.RiccatiSpatialDMonomialFiniteExpansionRecovery
import NlsGge.Hierarchy.RiccatiShiftedBranchProductRecovery28Second
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory
open scoped ContDiff

def riccatiIBPBranchExponentNativeRecovery28Second
    (r : Jet →₀ ℕ) (v w : Jet) : Jet →₀ ℕ :=
  (r - Finsupp.single w 1) + Finsupp.single (v.1, v.2 - 1) 1 +
    Finsupp.single (w.1, w.2 + 1) 1

/-- Exact finite polynomial branch expansion from the actual spatial
monomial-derivative formula. The removed multiplicity index `w` and the
shifted jet `w+1` are kept distinct in the checked product prerequisite. -/
theorem riccatiJetMonomial_spatialD_branchPolynomialExpansionNativeRecovery28Second
    (r : Jet →₀ ℕ) (c : ℤ) (v : Jet) (horder : 0 < v.2) :
    MvPolynomial.X (v.1, v.2 - 1) * spatialD (MvPolynomial.monomial r c) =
      ∑ w ∈ r.support,
        MvPolynomial.monomial (riccatiIBPBranchExponentNativeRecovery28Second r v w)
          (c * (r w : ℤ)) := by
  classical
  rw [spatialD_monomial_actual_factor_expansionNativeRecovery]
  simp only [MvPolynomial.smul_eq_C_mul, Finsupp.sum]
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hproduct := riccatiPoly_shifted_IBP_branch_productNativeRecovery28Second
    (r := r) (c := c) (v := v) (w := w)
  rw [riccatiPoly_intCast_eq_CNativeRecovery28] at hproduct
  simpa [riccatiIBPBranchExponentNativeRecovery28Second,
    add_comm, add_left_comm, add_assoc] using hproduct

/-- The actual smooth-periodic one-step IBP identity, expanded as the exact
finite sum of concrete monomial integrals. -/
theorem riccatiJetMonomial_periodic_ibp_finite_branchesNativeRecovery28Second
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (m : Jet →₀ ℕ) (c : ℤ) (v : Jet)
    (hv : v ∈ m.support) (horder : 0 < v.2) :
    (∫ x in (0 : ℝ)..1,
      riccatiJetEvaluation u x (MvPolynomial.monomial m c)) =
      - ∑ w ∈ (m - Finsupp.single v 1).support,
        ∫ x in (0 : ℝ)..1,
          riccatiJetEvaluation u x
            (MvPolynomial.monomial
              (riccatiIBPBranchExponentNativeRecovery28Second
                (m - Finsupp.single v 1) v w)
              (c * (((m - (Finsupp.single v (1 : ℕ) : Jet →₀ ℕ)) w : ℕ) : ℤ))) := by
  classical
  let r : Jet →₀ ℕ := m - Finsupp.single v 1
  let f : ℝ → ℂ := fun x =>
    riccatiJetEvaluation u x (MvPolynomial.X (v.1, v.2 - 1))
  let g : ℝ → ℂ := fun x =>
    riccatiJetEvaluation u x (spatialD (MvPolynomial.monomial r c))
  have hstep := riccatiJetMonomial_periodic_ibp_stepNativeRecovery
    u hu hper m c v hv horder
  have hpoly := riccatiJetMonomial_spatialD_branchPolynomialExpansionNativeRecovery28Second
    r c v horder
  have hsum :
      (∫ x in (0 : ℝ)..1, f x * g x) =
        ∑ w ∈ r.support,
          ∫ x in (0 : ℝ)..1,
            riccatiJetEvaluation u x
              (MvPolynomial.monomial
                (riccatiIBPBranchExponentNativeRecovery28Second r v w)
                (c * (r w : ℤ))) := by
    calc
      (∫ x in (0 : ℝ)..1, f x * g x) =
          ∫ x in (0 : ℝ)..1,
            riccatiJetEvaluation u x
              (MvPolynomial.X (v.1, v.2 - 1) * spatialD (MvPolynomial.monomial r c)) := by
                apply intervalIntegral.integral_congr
                intro x hx
                simp [f, g, riccatiJetEvaluation, polynomialEvaluation_mul]
      _ = ∫ x in (0 : ℝ)..1,
            riccatiJetEvaluation u x
              (∑ w ∈ r.support,
                MvPolynomial.monomial
                  (riccatiIBPBranchExponentNativeRecovery28Second r v w)
                  (c * (r w : ℤ))) := by rw [hpoly]
      _ = _ := by
        simpa [riccatiJetEvaluation, polynomialEvaluation, map_sum] using
          (riccatiJetEvaluation_integral_finset_sumNativeRecoverySecond
            u hu r.support (fun w =>
              MvPolynomial.monomial
                (riccatiIBPBranchExponentNativeRecovery28Second r v w)
                (c * (r w : ℤ))))
  dsimp [r] at hsum
  simpa [f, g, r] using hstep.trans (congrArg Neg.neg hsum)

end NlsGge.HierarchyRiccati.Core

end

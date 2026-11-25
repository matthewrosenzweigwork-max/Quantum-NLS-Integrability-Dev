import NlsGge.Hierarchy.RiccatiChargeRemainderNoQuadraticSupportSecond
import NlsGge.Hierarchy.RiccatiRecurrenceBidegreeInductionThird
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open MvPolynomial

/-- Every exponent in the actual formal charge density has the source
weight and gauge obtained from the actual Riccati bidegree theorem. -/
theorem formalChargeIntegrand_support_bidegree (j : ℕ) (m : Jet →₀ ℕ)
    (hm : m ∈ (formalChargeIntegrand j).support) :
    riccatiJetBidegreeAfterComponents m = (2 * j + 2, 0) := by
  classical
  have hscalar : (-1 : ℤ) ^ (j + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold formalChargeIntegrand at hm
  rw [mul_assoc, MvPolynomial.C_mul'] at hm
  rw [MvPolynomial.support_smul_eq hscalar, MvPolynomial.support_X_mul] at hm
  rcases Finset.mem_map.mp hm with ⟨n, hn, hmap⟩
  have hmEq : Finsupp.single (false, 0) 1 + n = m := by simpa using hmap
  have hp := riccati_p_has_bidegree_after_components (2 * j + 1) (by omega)
  have hnb := hp n hn
  have hnWeight : riccatiJetWeightHomAfterComponents n = 2 * j + 1 := by
    simpa [riccatiJetBidegreeAfterComponents] using congrArg Prod.fst hnb
  have hnGauge : riccatiJetGaugeHomAfterComponents n = 1 := by
    simpa [riccatiJetBidegreeAfterComponents] using congrArg Prod.snd hnb
  rw [← hmEq]
  apply Prod.ext
  · change riccatiJetWeightHomAfterComponents
        (Finsupp.single (false, 0) 1 + n) = 2 * j + 2
    rw [map_add, riccatiJetWeightHomAfterComponents_single, hnWeight]
    omega
  · change riccatiJetGaugeHomAfterComponents
        (Finsupp.single (false, 0) 1 + n) = 0
    rw [map_add, riccatiJetGaugeHomAfterComponents_single, hnGauge]
    norm_num

/-- Subtracting the checked quadratic component leaves support inside the
actual formal charge support: every degree-two coefficient cancels. -/
theorem formalChargeNonlinearRemainder_support_subset_charge (j : ℕ) :
    (formalChargeNonlinearRemainder j).support ⊆ (formalChargeIntegrand j).support := by
  classical
  intro m hm
  have hmUnion := MvPolynomial.support_sub Jet (formalChargeIntegrand j)
    (formalChargeQuadraticMainTerm j) hm
  rcases Finset.mem_union.mp hmUnion with hdensity | hmain
  · exact hdensity
  · have hmainHom : (formalChargeQuadraticMainTerm j).IsHomogeneous 2 := by
      unfold formalChargeQuadraticMainTerm
      rw [← formalChargeIntegrand_degreeTwoComponent j]
      exact MvPolynomial.homogeneousComponent_isHomogeneous 2 (formalChargeIntegrand j)
    have hsum : 2 = ∑ v ∈ m.support, m v := hmainHom.degree_eq_sum_deg_support hmain
    have hmDegree : m.degree = 2 := by
      rw [Finsupp.degree_apply]
      exact hsum.symm
    have hcoeff := formalCharge_coefficient_degreeTwo j m hmDegree
    have hmainCoeff : (formalChargeQuadraticMainTerm j).coeff m ≠ 0 :=
      Finsupp.mem_support_iff.mp hmain
    have hdensityCoeff : (formalChargeIntegrand j).coeff m ≠ 0 := by
      simpa [hcoeff] using hmainCoeff
    exact Finsupp.mem_support_iff.mpr hdensityCoeff

/-- Every exponent in the actual nonlinear remainder retains the charge's
weight and gauge bidegree. -/
theorem formalChargeNonlinearRemainder_support_bidegree (j : ℕ)
    (m : Jet →₀ ℕ) (hm : m ∈ (formalChargeNonlinearRemainder j).support) :
    riccatiJetBidegreeAfterComponents m = (2 * j + 2, 0) :=
  formalChargeIntegrand_support_bidegree j m
    (formalChargeNonlinearRemainder_support_subset_charge j hm)

end NlsGge.HierarchyRiccati.Core

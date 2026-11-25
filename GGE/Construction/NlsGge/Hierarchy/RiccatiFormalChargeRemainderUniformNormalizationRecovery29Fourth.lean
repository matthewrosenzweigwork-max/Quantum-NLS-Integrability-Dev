import NlsGge.Hierarchy.RiccatiFinitePeriodicMonomialNormalizerUniformRecovery28Seventh
import NlsGge.Hierarchy.RiccatiFormalChargeIntervalIntegrabilitySplitRecovery29Second
import NlsGge.Hierarchy.RiccatiChargeRemainderSupportOrderBoundsAfterBidegreeThirdRecoveryThird
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory
open scoped ContDiff

/-- The concrete support-restricted normalizer chooses each monomial witness
from the checked uniform theorem. Its definition depends only on the actual
formal remainder exponent and coefficient, never on a field. -/
noncomputable def formalChargeRemainderNormalizedTermNativeRecovery29Fourth
    (j : ℕ) (m : Jet →₀ ℕ) : Poly := by
  classical
  by_cases hm : m ∈ (formalChargeNonlinearRemainder j).support
  · have horder := formalChargeNonlinearRemainder_support_order_boundsNativeRecovery j m hm
    have hcount : riccatiJetDerivativeOrderWeightNativeRecovery m ≤ 2 * j - 2 := by
      simpa [riccatiJetDerivativeOrderWeightNativeRecovery,
        riccatiJetDerivativeOrderSumNativeRecovery, Finsupp.weight_apply] using horder.2
    exact Classical.choose
      (riccatiJetMonomial_periodic_normalize_uniformNativeRecovery28Fifth
        j m ((formalChargeNonlinearRemainder j).coeff m) hcount)
  · exact 0

theorem formalChargeRemainderNormalizedTerm_specNativeRecovery29Fourth
    (j : ℕ) (m : Jet →₀ ℕ)
    (hm : m ∈ (formalChargeNonlinearRemainder j).support) :
    HasJetOrderAtMostNativeRecovery j
      (formalChargeRemainderNormalizedTermNativeRecovery29Fourth j m) ∧
    HasJetFactorDegreeOnSupportUniformRecovery28Seventh
      (formalChargeRemainderNormalizedTermNativeRecovery29Fourth j m) m.degree ∧
    HasRiccatiJetBidegreeAfterComponents
      (formalChargeRemainderNormalizedTermNativeRecovery29Fourth j m)
      (riccatiJetBidegreeAfterComponents m) ∧
    ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
      (hper : Function.Periodic u 1),
      (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x
          (MvPolynomial.monomial m ((formalChargeNonlinearRemainder j).coeff m))) =
      (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x
          (formalChargeRemainderNormalizedTermNativeRecovery29Fourth j m)) := by
  classical
  simp only [formalChargeRemainderNormalizedTermNativeRecovery29Fourth, dif_pos hm]
  exact Classical.choose_spec
    (riccatiJetMonomial_periodic_normalize_uniformNativeRecovery28Fifth
      j m ((formalChargeNonlinearRemainder j).coeff m) (by
        have horder := formalChargeNonlinearRemainder_support_order_boundsNativeRecovery j m hm
        simpa [riccatiJetDerivativeOrderWeightNativeRecovery,
          riccatiJetDerivativeOrderSumNativeRecovery, Finsupp.weight_apply] using horder.2))

/-- The single fixed polynomial obtained by summing the normalized witnesses
for the actual finite support of the nonlinear formal Riccati charge. -/
noncomputable def formalChargeRemainderNormalizedUniformNativeRecovery29Fourth
    (j : ℕ) : Poly :=
  ∑ m ∈ (formalChargeNonlinearRemainder j).support,
    formalChargeRemainderNormalizedTermNativeRecovery29Fourth j m

private theorem hasRiccatiJetBidegree_finset_sumNativeRecovery29Fourth
    {ι : Type*} (s : Finset ι) (P : ι → Poly) {d : ℕ × ℤ}
    (hP : ∀ i ∈ s, HasRiccatiJetBidegreeAfterComponents (P i) d) :
    HasRiccatiJetBidegreeAfterComponents (∑ i ∈ s, P i) d := by
  classical
  intro m hm
  have hmem : m ∈ Finset.biUnion s (fun i => (P i).support) :=
    MvPolynomial.support_sum hm
  obtain ⟨i, hi, him⟩ := Finset.mem_biUnion.mp hmem
  exact hP i hi m him

def HasJetFactorCountAtLeastNativeRecovery29 (P : Poly) (q : ℕ) : Prop :=
  ∀ m ∈ P.support, q ≤ m.degree

theorem formalChargeRemainderNormalizedUniform_propertiesNativeRecovery29Fourth
    (j : ℕ) :
    HasJetOrderAtMostNativeRecovery j
      (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j) ∧
    HasJetFactorCountAtLeastNativeRecovery29
      (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j) 4 ∧
    HasRiccatiJetBidegreeAfterComponents
      (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j) (2 * j + 2, 0) ∧
    (∀ m ∈ (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j).support,
      m.degree ≤ 2 * j + 2) := by
  classical
  let s := (formalChargeNonlinearRemainder j).support
  let Q := formalChargeRemainderNormalizedTermNativeRecovery29Fourth j
  have hlow : ∀ m ∈ s, HasJetOrderAtMostNativeRecovery j (Q m) := by
    intro m hm
    exact (formalChargeRemainderNormalizedTerm_specNativeRecovery29Fourth j m hm).1
  have hlowSum := hasJetOrderAtMost_finset_sumNativeRecovery s Q hlow
  have hcount : ∀ m ∈ s, HasJetFactorDegreeOnSupportUniformRecovery28Seventh
      (Q m) m.degree := by
    intro m hm
    exact (formalChargeRemainderNormalizedTerm_specNativeRecovery29Fourth j m hm).2.1
  have hcountSum : HasJetFactorCountAtLeastNativeRecovery29
      (∑ m ∈ s, Q m) 4 := by
    intro n hn
    have hnmem : n ∈ Finset.biUnion s (fun m => (Q m).support) :=
      MvPolynomial.support_sum hn
    obtain ⟨m, hm, hnm⟩ := Finset.mem_biUnion.mp hnmem
    have hsource := formalChargeNonlinearRemainder_support_order_boundsNativeRecovery j m hm
    have hfactor := hcount m hm n hnm
    calc
      4 ≤ m.degree := hsource.1
      _ = n.degree := hfactor.symm
  have hbidegree : ∀ m ∈ s,
      HasRiccatiJetBidegreeAfterComponents (Q m) (2 * j + 2, 0) := by
    intro m hm
    have hterm := (formalChargeRemainderNormalizedTerm_specNativeRecovery29Fourth j m hm).2.2.1
    rw [formalChargeNonlinearRemainder_support_bidegree j m hm] at hterm
    exact hterm
  have hbidegreeSum := hasRiccatiJetBidegree_finset_sumNativeRecovery29Fourth s Q hbidegree
  have hdegree : ∀ n ∈ (∑ m ∈ s, Q m).support, n.degree ≤ 2 * j + 2 := by
    intro n hn
    have hweight : riccatiJetWeightHomAfterComponents n = 2 * j + 2 := by
      simpa [riccatiJetBidegreeAfterComponents] using
        congrArg Prod.fst (hbidegreeSum n hn)
    rw [riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery] at hweight
    omega
  simpa [formalChargeRemainderNormalizedUniformNativeRecovery29Fourth, s, Q] using
    And.intro hlowSum (And.intro hcountSum (And.intro hbidegreeSum hdegree))

theorem formalChargeRemainder_integral_eq_uniformNormalizedNativeRecovery29Fourth
    (j : ℕ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1,
      riccatiJetEvaluation u x (formalChargeNonlinearRemainder j)) =
    (∫ x in (0 : ℝ)..1,
      riccatiJetEvaluation u x
        (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j)) := by
  classical
  let s := (formalChargeNonlinearRemainder j).support
  let Q := formalChargeRemainderNormalizedTermNativeRecovery29Fourth j
  calc
    (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x (formalChargeNonlinearRemainder j)) =
      ∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x
          (∑ m ∈ s, MvPolynomial.monomial m
            ((formalChargeNonlinearRemainder j).coeff m)) := by
              have hsumPoly : formalChargeNonlinearRemainder j =
                  ∑ m ∈ s, MvPolynomial.monomial m
                    ((formalChargeNonlinearRemainder j).coeff m) := by
                simpa [s] using MvPolynomial.as_sum (formalChargeNonlinearRemainder j)
              exact congrArg
                (fun p : Poly => ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x p)
                hsumPoly
    _ = ∑ m ∈ s,
          ∫ x in (0 : ℝ)..1,
            riccatiJetEvaluation u x
              (MvPolynomial.monomial m ((formalChargeNonlinearRemainder j).coeff m)) :=
        riccatiJetEvaluation_integral_finset_sumNativeRecoverySecond u hu s
          (fun m => MvPolynomial.monomial m ((formalChargeNonlinearRemainder j).coeff m))
    _ = ∑ m ∈ s, ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (Q m) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact (formalChargeRemainderNormalizedTerm_specNativeRecovery29Fourth j m hm).2.2.2
          u hu hper
    _ = ∫ x in (0 : ℝ)..1,
          riccatiJetEvaluation u x (∑ m ∈ s, Q m) := by
        symm
        exact riccatiJetEvaluation_integral_finset_sumNativeRecoverySecond u hu s Q

theorem formalChargeIntegrand_integral_quadratic_plus_uniformRemainderNativeRecovery29Fourth
    (j : ℕ) (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalChargeIntegrand j)) =
      (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x (formalChargeQuadraticMainTerm j)) +
      (∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x
          (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j)) := by
  calc
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalChargeIntegrand j)) =
        (∫ x in (0 : ℝ)..1,
          riccatiJetEvaluation u x (formalChargeQuadraticMainTerm j)) +
        (∫ x in (0 : ℝ)..1,
          riccatiJetEvaluation u x (formalChargeNonlinearRemainder j)) :=
      formalChargeIntegrand_integral_splitNativeRecovery29Second j u hu
    _ = (∫ x in (0 : ℝ)..1,
          riccatiJetEvaluation u x (formalChargeQuadraticMainTerm j)) +
        (∫ x in (0 : ℝ)..1,
          riccatiJetEvaluation u x
            (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j)) := by
      congr 1
      exact formalChargeRemainder_integral_eq_uniformNormalizedNativeRecovery29Fourth j u hu hper

end NlsGge.HierarchyRiccati.Core

end

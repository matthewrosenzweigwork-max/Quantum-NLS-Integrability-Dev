import NlsGge.Hierarchy.RiccatiChargeRemainderSupportOrderBoundsAfterBidegreeThirdRecoveryThird
import NlsGge.Hierarchy.RiccatiFormalChargeRemainderUniformNormalizationRecovery29Fourth

                                                                                                                                                                                                                   
                                                                                                                 
                                                                      
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M

open NlsGge.HierarchyRiccati.Core
open MeasureTheory
open scoped ContDiff

def weightedDegree (q : Jet →₀ ℕ) : ℕ :=
  riccatiJetWeightHomAfterComponents q

def gaugeCharge (q : Jet →₀ ℕ) : ℤ :=
  riccatiJetGaugeHomAfterComponents q

def fieldCount (q : Jet →₀ ℕ) : ℕ :=
  q.sum (fun _ e => e)

def normalizedChargeRemainder (m : ℕ) : Poly :=
  formalChargeRemainderNormalizedUniformNativeRecovery29Fourth m

namespace M004Aux

theorem fieldCount_eq_degree (q : Jet →₀ ℕ) : fieldCount q = q.degree := by
  rw [Finsupp.degree_apply]; rfl

end M004Aux

open M004Aux

theorem riccati_monomial_grading
    (m : ℕ) (hm : 1 ≤ m)
    (q : Jet →₀ ℕ)
    (hq : q ∈ (formalChargeIntegrand m).support) :
    weightedDegree q = 2 * m + 2 ∧
    gaugeCharge q = 0 ∧
    Even (fieldCount q) ∧
    (q ∈ (formalChargeNonlinearRemainder m).support →
      4 ≤ fieldCount q ∧
      riccatiJetDerivativeOrderSumNativeRecovery q =
        2 * m + 2 - fieldCount q ∧
      riccatiJetDerivativeOrderSumNativeRecovery q ≤ 2 * m - 2) := by
  have hb := formalChargeIntegrand_support_bidegree m q hq
  have hw : riccatiJetWeightHomAfterComponents q = 2 * m + 2 := congrArg Prod.fst hb
  have hg : riccatiJetGaugeHomAfterComponents q = 0 := congrArg Prod.snd hb
  have hev := riccatiJetGauge_zero_implies_degree_evenNativeRecovery q hg
  refine ⟨hw, hg, by rwa [fieldCount_eq_degree], fun hr => ?_⟩
  obtain ⟨h4, hle⟩ := formalChargeNonlinearRemainder_support_order_boundsNativeRecovery m q hr
  have hsum := riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery q
  rw [fieldCount_eq_degree]
  exact ⟨h4, by omega, hle⟩

theorem riccati_normalized_remainder_monomial_grading
    (m : ℕ) (hm : 1 ≤ m)
    (q : Jet →₀ ℕ)
    (hq : q ∈ (normalizedChargeRemainder m).support) :
    weightedDegree q = 2 * m + 2 ∧
    gaugeCharge q = 0 ∧
    Even (fieldCount q) ∧
    4 ≤ fieldCount q ∧
    riccatiJetDerivativeOrderSumNativeRecovery q =
      2 * m + 2 - fieldCount q ∧
    riccatiJetDerivativeOrderSumNativeRecovery q ≤ 2 * m - 2 ∧
    ∀ v ∈ q.support, v.2 ≤ m - 1 := by
  obtain ⟨hlow, hcount, hbi, -⟩ :=
    formalChargeRemainderNormalizedUniform_propertiesNativeRecovery29Fourth m
  have hb := hbi q hq
  have hw : riccatiJetWeightHomAfterComponents q = 2 * m + 2 := congrArg Prod.fst hb
  have hg : riccatiJetGaugeHomAfterComponents q = 0 := congrArg Prod.snd hb
  have hev := riccatiJetGauge_zero_implies_degree_evenNativeRecovery q hg
  have h4 : 4 ≤ q.degree := hcount q hq
  have hsum := riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery q
  refine ⟨hw, hg, by rwa [fieldCount_eq_degree], by rw [fieldCount_eq_degree]; exact h4,
    by rw [fieldCount_eq_degree]; omega, by omega, hlow q hq⟩

theorem riccati_remainder_integral_eq_normalized
    (m : ℕ) (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1,
      riccatiJetEvaluation u x (formalChargeNonlinearRemainder m)) =
    (∫ x in (0 : ℝ)..1,
      riccatiJetEvaluation u x (normalizedChargeRemainder m)) :=
  formalChargeRemainder_integral_eq_uniformNormalizedNativeRecovery29Fourth m u hu hper

theorem riccati_monomial_grading_general
    (k : ℕ) (q : NlsGge.HierarchyRiccati.Core.Jet →₀ ℕ)
    (hq : q ∈
      (MvPolynomial.X (false, 0) *
        NlsGge.HierarchyRiccati.Core.p (k + 1)).support) :
    weightedDegree q = k + 2 ∧ gaugeCharge q = 0 ∧
    Even (fieldCount q) := by
  classical
  rw [MvPolynomial.support_X_mul] at hq
  rcases Finset.mem_map.mp hq with ⟨n, hn, hmap⟩
  have hmEq : Finsupp.single (false, 0) 1 + n = q := by simpa using hmap
  have hnb := riccati_p_has_bidegree_after_components (k + 1) (by omega) n hn
  have hnWeight : riccatiJetWeightHomAfterComponents n = k + 1 := by
    simpa [riccatiJetBidegreeAfterComponents] using congrArg Prod.fst hnb
  have hnGauge : riccatiJetGaugeHomAfterComponents n = 1 := by
    simpa [riccatiJetBidegreeAfterComponents] using congrArg Prod.snd hnb
  have hw : riccatiJetWeightHomAfterComponents q = k + 2 := by
    rw [← hmEq, map_add, riccatiJetWeightHomAfterComponents_single, hnWeight]
    omega
  have hg : riccatiJetGaugeHomAfterComponents q = 0 := by
    rw [← hmEq, map_add, riccatiJetGaugeHomAfterComponents_single, hnGauge]
    norm_num
  have hev := riccatiJetGauge_zero_implies_degree_evenNativeRecovery q hg
  exact ⟨hw, hg, by rwa [fieldCount_eq_degree]⟩


end NlsGge.ThirdConsultation.M
end

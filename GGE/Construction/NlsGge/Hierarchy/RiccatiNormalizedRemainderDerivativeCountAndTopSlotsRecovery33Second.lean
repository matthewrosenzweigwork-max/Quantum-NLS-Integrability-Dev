import NlsGge.Hierarchy.RiccatiFormalChargeRemainderUniformNormalizationRecovery29Fourth
import NlsGge.Hierarchy.RiccatiActualMonomialFiniteSlotsRecovery31Fourth
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

/-- Every exponent in the actual fixed normalized charge remainder has the
same total derivative-count bound as its source charge. This is derived from
the normalized polynomial's own bidegree and factor-count properties. -/
theorem formalChargeRemainderNormalized_derivativeOrderSum_leRecovery33Second
    (j : ℕ) (q : Jet →₀ ℕ)
    (hq : q ∈ (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j).support) :
    riccatiJetDerivativeOrderSumNativeRecovery q ≤ 2 * j - 2 := by
  have hprop := formalChargeRemainderNormalizedUniform_propertiesNativeRecovery29Fourth j
  have hfactor : 4 ≤ q.degree := hprop.2.1 q hq
  have hbidegree := hprop.2.2.1 q hq
  have hweight : riccatiJetWeightHomAfterComponents q = 2 * j + 2 := by
    simpa [riccatiJetBidegreeAfterComponents] using congrArg Prod.fst hbidegree
  rw [riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery] at hweight
  omega

/-- For a fixed paper cutoff `M`, every supported monomial of every actual
normalized charge `j ≤ M` has at most two order-`M-1` occurrences. If `j<M`,
the normalized per-jet cutoff `order ≤ j-1` rules out such slots entirely;
only the boundary charge `j=M` needs the total derivative-count estimate. -/
theorem formalChargeRemainderNormalized_topSlotCard_le_twoRecovery33Second
    (M j : ℕ) (hM : 2 ≤ M) (hjM : j ≤ M) (q : Jet →₀ ℕ)
    (hq : q ∈ (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j).support) :
    ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun s => s.1.2 + 1 = M)).card ≤ 2 := by
  by_cases hj : j < M
  · have hprop := formalChargeRemainderNormalizedUniform_propertiesNativeRecovery29Fourth j
    have hlow := hprop.1 q hq
    have hmult : riccatiTopJetSlotMultiplicityMinimumRecovery30Third M q = 0 := by
      unfold riccatiTopJetSlotMultiplicityMinimumRecovery30Third
      apply Finset.sum_eq_zero
      intro v hv
      by_cases htop : v.2 + 1 = M
      · have horder := hlow v hv
        have hle : v.2 + 1 ≤ j := by omega
        have hFalse : False := by omega
        simp only [htop]
        exact False.elim hFalse
      · simp [htop]
    rw [riccatiActualMonomialSlotFinset_topCardRecovery31Fourth, hmult]
    omega
  · have hjEq : j = M := by omega
    subst j
    exact riccatiActualMonomialSlotFinset_topCard_le_twoRecovery31Fourth
      M hM q (formalChargeRemainderNormalized_derivativeOrderSum_leRecovery33Second
        M q hq)

end NlsGge.HierarchyRiccati.Core

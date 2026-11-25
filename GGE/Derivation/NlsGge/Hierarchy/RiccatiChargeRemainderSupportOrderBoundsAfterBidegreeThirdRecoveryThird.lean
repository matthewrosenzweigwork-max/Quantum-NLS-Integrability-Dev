import NlsGge.Hierarchy.RiccatiChargeRemainderBidegreeAfterCancellationThird
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati.Core

open MvPolynomial

/-- Total derivative order represented by an exponent of the actual jet
polynomial. -/
def riccatiJetDerivativeOrderSumNativeRecovery (m : Jet →₀ ℕ) : ℕ :=
  m.sum fun v e => e * v.2

/-- The source weight is the number of field factors plus their total
derivative order. -/
theorem riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery
    (m : Jet →₀ ℕ) :
    riccatiJetWeightHomAfterComponents m =
      m.degree + riccatiJetDerivativeOrderSumNativeRecovery m := by
  classical
  rw [Finsupp.degree_apply]
  unfold riccatiJetWeightHomAfterComponents riccatiJetDerivativeOrderSumNativeRecovery
  change (∑ v ∈ m.support, m v * (v.2 + 1)) =
    (∑ v ∈ m.support, m v) + ∑ v ∈ m.support, m v * v.2
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  simp [Nat.mul_add, Nat.add_comm]

/-- A zero gauge exponent has an even number of field factors. This proof
decomposes the finite support by the Boolean sign and proves each filtered
sum by explicit membership, rather than asking `simp` to reconcile signed
Boolean indicators with naturals. -/
theorem riccatiJetGauge_zero_implies_degree_evenNativeRecovery
    (m : Jet →₀ ℕ)
    (hg : riccatiJetGaugeHomAfterComponents m = 0) : Even m.degree := by
  classical
  let S := m.support
  let qplus : ℕ := ∑ v ∈ S.filter (fun v : Jet => v.1), m v
  let qminus : ℕ := ∑ v ∈ S.filter (fun v : Jet => ¬ v.1), m v
  have hdegree : m.degree = qplus + qminus := by
    rw [Finsupp.degree_apply]
    change (∑ v ∈ S, m v) = qplus + qminus
    rw [← Finset.sum_filter_add_sum_filter_not S (fun v : Jet => v.1)]
  have hplus :
      (∑ v ∈ S.filter (fun v : Jet => v.1),
        if v.1 then (m v : ℤ) else -(m v : ℤ)) = (qplus : ℤ) := by
    change (∑ v ∈ S.filter (fun v : Jet => v.1),
        if v.1 then (m v : ℤ) else -(m v : ℤ)) =
      ((∑ v ∈ S.filter (fun v : Jet => v.1), m v : ℕ) : ℤ)
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [Finset.mem_filter] at hv
    simp [hv.2]
  have hminus :
      (∑ v ∈ S.filter (fun v : Jet => ¬ v.1),
        if v.1 then (m v : ℤ) else -(m v : ℤ)) = -(qminus : ℤ) := by
    change (∑ v ∈ S.filter (fun v : Jet => ¬ v.1),
        if v.1 then (m v : ℤ) else -(m v : ℤ)) =
      -((∑ v ∈ S.filter (fun v : Jet => ¬ v.1), m v : ℕ) : ℤ)
    rw [Nat.cast_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [Finset.mem_filter] at hv
    simp [hv.2]
  have hgauge : riccatiJetGaugeHomAfterComponents m = (qplus : ℤ) - qminus := by
    change (∑ v ∈ S, if v.1 then (m v : ℤ) else -(m v : ℤ)) = _
    rw [← Finset.sum_filter_add_sum_filter_not S (fun v : Jet => v.1)]
    rw [hplus, hminus]
    ring
  have hcast : (qplus : ℤ) = qminus := by
    rw [hgauge] at hg
    exact sub_eq_zero.mp hg
  have hnat : qplus = qminus := by exact_mod_cast hcast
  refine ⟨qplus, ?_⟩
  rw [hdegree, hnat]

/-- Every exponent in the nonlinear remainder has at least four field
factors and at most `2*j-2` total derivatives. This is a source-support
bound only; it does not perform the separate integration-by-parts
normalization that bounds each individual derivative order. -/
theorem formalChargeNonlinearRemainder_support_order_boundsNativeRecovery
    (j : ℕ) (m : Jet →₀ ℕ)
    (hm : m ∈ (formalChargeNonlinearRemainder j).support) :
    4 ≤ m.degree ∧
      riccatiJetDerivativeOrderSumNativeRecovery m ≤ 2 * j - 2 := by
  have hbidegree := formalChargeNonlinearRemainder_support_bidegree j m hm
  have hweight : riccatiJetWeightHomAfterComponents m = 2 * j + 2 :=
    congrArg Prod.fst hbidegree
  have hgauge : riccatiJetGaugeHomAfterComponents m = 0 :=
    congrArg Prod.snd hbidegree
  have heven := riccatiJetGauge_zero_implies_degree_evenNativeRecovery m hgauge
  have hdegree_ne_two : m.degree ≠ 2 :=
    formalChargeNonlinearRemainder_support_degree_ne_two j m hm
  have hdegree_pos : 0 < m.degree := by
    by_contra hnot
    have hzero : m.degree = 0 := by omega
    have hmzero : m = 0 := (Finsupp.degree_eq_zero_iff m).mp hzero
    subst m
    simp [riccatiJetWeightHomAfterComponents] at hweight
  have hdegree_four : 4 ≤ m.degree := by
    rcases heven with ⟨k, hk⟩
    omega
  rw [riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery] at hweight
  exact ⟨hdegree_four, by omega⟩

end NlsGge.HierarchyRiccati.Core

import NlsGge.Hierarchy.RiccatiFinitePeriodicIBPBranchesRecovery28Second
import NlsGge.Hierarchy.RiccatiIBPBranchBidegreeRecovery28Fourth
import NlsGge.Hierarchy.RiccatiJetOrderLowPolynomialClosureRecovery
import NlsGge.Hierarchy.RiccatiJetEvaluationFiniteIntervalSumRecoverySecond
import NlsGge.Hierarchy.RiccatiMonomialIBPDerivativeCountPreservationRecoverySecond
import NlsGge.Hierarchy.RiccatiHighJetIndexedWeightMinimumRecovery
import NlsGge.Hierarchy.RiccatiDerivativeExcessAndPeriodicEvaluatorRecoverySecond
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory
open scoped ContDiff

private theorem riccatiJet_exists_high_factor_of_positive_excessUniformRecovery28Seventh
    (j : ℕ) (m : Jet →₀ ℕ)
    (hE : 0 < riccatiJetDerivativeExcessNativeRecovery j m) :
    ∃ v ∈ m.support, j ≤ v.2 := by
  classical
  by_contra h
  push_neg at h
  have hlowExcess : ∀ v ∈ m.support, v.2 - (j - 1) = 0 := by
    intro v hv
    have hvlt : v.2 < j := h v hv
    omega
  have hweight :
      riccatiJetDerivativeExcessNativeRecovery j m =
        ∑ v ∈ m.support, m v * (v.2 - (j - 1)) := by
    simp [riccatiJetDerivativeExcessNativeRecovery,
      Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  rw [hweight] at hE
  have hzero : (∑ v ∈ m.support, m v * (v.2 - (j - 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    simp [hlowExcess v hv]
  omega

def HasJetFactorDegreeOnSupportUniformRecovery28Seventh (P : Poly) (d : ℕ) : Prop :=
  ∀ m ∈ P.support, m.degree = d

private theorem riccatiHasFactorDegree_sumUniformRecovery28Seventh
    {ι : Type*} (s : Finset ι) (f : ι → Poly) {d : ℕ}
    (hf : ∀ i ∈ s, HasJetFactorDegreeOnSupportUniformRecovery28Seventh (f i) d) :
    HasJetFactorDegreeOnSupportUniformRecovery28Seventh (∑ i ∈ s, f i) d := by
  classical
  intro m hm
  have hmem : m ∈ Finset.biUnion s (fun i => (f i).support) := by
    exact MvPolynomial.support_sum hm
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp hmem
  exact hf i hi m hmi

private theorem riccatiHasFactorDegree_negUniformRecovery28Seventh
    {P : Poly} {d : ℕ}
    (hP : HasJetFactorDegreeOnSupportUniformRecovery28Seventh P d) :
    HasJetFactorDegreeOnSupportUniformRecovery28Seventh (-P) d := by
  intro m hm
  apply hP m
  simpa only [MvPolynomial.support_neg] using hm

private theorem riccatiHasFactorDegree_monomialUniformRecovery28Seventh
    (m : Jet →₀ ℕ) (a : ℤ) :
    HasJetFactorDegreeOnSupportUniformRecovery28Seventh
      (MvPolynomial.monomial m a) m.degree := by
  classical
  intro n hn
  have hnm : n = m := by
    exact Finset.mem_singleton.mp
      (MvPolynomial.support_monomial_subset hn)
  simpa [hnm]

private theorem riccatiHasBidegree_sumUniformRecovery28Seventh
    {ι : Type*} (s : Finset ι) (f : ι → Poly) {d : ℕ × ℤ}
    (hf : ∀ i ∈ s, HasRiccatiJetBidegreeAfterComponents (f i) d) :
    HasRiccatiJetBidegreeAfterComponents (∑ i ∈ s, f i) d := by
  classical
  intro m hm
  have hmem : m ∈ Finset.biUnion s (fun i => (f i).support) := by
    exact MvPolynomial.support_sum hm
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp hmem
  exact hf i hi m hmi

private theorem riccatiHasBidegree_negUniformRecovery28Seventh
    {P : Poly} {d : ℕ × ℤ}
    (hP : HasRiccatiJetBidegreeAfterComponents P d) :
    HasRiccatiJetBidegreeAfterComponents (-P) d := by
  intro m hm
  apply hP m
  simpa only [MvPolynomial.support_neg] using hm

private theorem riccatiHasBidegree_monomialUniformRecovery28Seventh
    (m : Jet →₀ ℕ) (a : ℤ) :
    HasRiccatiJetBidegreeAfterComponents (MvPolynomial.monomial m a)
      (riccatiJetBidegreeAfterComponents m) := by
  classical
  intro n hn
  have hnm : n = m := by
    exact Finset.mem_singleton.mp
      (MvPolynomial.support_monomial_subset hn)
  simpa [hnm]

/-- A single polynomial, selected independently of the smooth periodic field,
normalizes every field integral. Its support has order at most `j-1`, and its
full source bidegree (field weight and signed gauge) is retained. -/
theorem riccatiJetMonomial_periodic_normalize_uniformNativeRecovery28Fifth
    (j : ℕ) (m : Jet →₀ ℕ) (c : ℤ)
    (hcount : riccatiJetDerivativeOrderWeightNativeRecovery m ≤ 2 * j - 2) :
    ∃ P : Poly,
      HasJetOrderAtMostNativeRecovery j P ∧
      HasJetFactorDegreeOnSupportUniformRecovery28Seventh P m.degree ∧
      HasRiccatiJetBidegreeAfterComponents P
        (riccatiJetBidegreeAfterComponents m) ∧
      ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
        (hper : Function.Periodic u 1),
        (∫ x in (0 : ℝ)..1,
          riccatiJetEvaluation u x (MvPolynomial.monomial m c)) =
        (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x P) := by
  classical
  let E := riccatiJetDerivativeExcessNativeRecovery j
  let D := riccatiJetDerivativeOrderWeightNativeRecovery
  let J : (ℝ → ℂ) → (Jet →₀ ℕ) → ℤ → ℂ := fun u q a =>
    ∫ x in (0 : ℝ)..1,
      riccatiJetEvaluation u x (MvPolynomial.monomial q a)
  have hmain : ∀ e : ℕ, ∀ q : Jet →₀ ℕ, ∀ a : ℤ,
      E q = e → D q ≤ 2 * j - 2 →
        ∃ P : Poly,
          HasJetOrderAtMostNativeRecovery j P ∧
          HasJetFactorDegreeOnSupportUniformRecovery28Seventh P q.degree ∧
          HasRiccatiJetBidegreeAfterComponents P
            (riccatiJetBidegreeAfterComponents q) ∧
          ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
            (hper : Function.Periodic u 1),
            J u q a =
              ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x P := by
    intro e
    induction e using Nat.strong_induction_on with
    | h e ih =>
      intro q a he hqcount
      have hmonomialLow :
          E q = 0 → HasJetOrderAtMostNativeRecovery j
            (MvPolynomial.monomial q a) := by
        intro hzero
        intro n hn v hv
        have hnq : n = q := by
          exact Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hn)
        subst n
        have hterm : v.2 - (j - 1) ≤ E q :=
          Finsupp.le_weight_of_ne_zero'
            (w := fun z : Jet => z.2 - (j - 1))
            (Finsupp.mem_support_iff.mp hv)
        change v.2 ≤ j - 1
        omega
      by_cases hjSmall : j ≤ 1
      · have hDzero : D q = 0 := by
          have hupper : 2 * j - 2 = 0 := by omega
          omega
        have hqLow : HasJetOrderAtMostNativeRecovery j
            (MvPolynomial.monomial q a) := by
          intro n hn v hv
          have hnq : n = q := by
            exact Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hn)
          subst n
          have hterm := riccatiJetDerivativeOrderWeight_coordinate_leNativeRecovery q v hv
          have hpos : 0 < q v := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
          have hvzero : v.2 = 0 := by
            have hterm0 : q v * v.2 ≤ 0 := by
              change q v * v.2 ≤ D q at hterm
              rw [hDzero] at hterm
              exact hterm
            have htermzero : q v * v.2 = 0 := Nat.eq_zero_of_le_zero hterm0
            exact (Nat.mul_eq_zero.mp htermzero).resolve_left (Nat.ne_of_gt hpos)
          change v.2 ≤ j - 1
          omega
        exact ⟨MvPolynomial.monomial q a, hqLow,
          riccatiHasFactorDegree_monomialUniformRecovery28Seventh q a,
          riccatiHasBidegree_monomialUniformRecovery28Seventh q a,
          by intro u hu hper; rfl⟩
      · have hj : 2 ≤ j := by omega
        by_cases hEzero : E q = 0
        · exact ⟨MvPolynomial.monomial q a, hmonomialLow hEzero,
            riccatiHasFactorDegree_monomialUniformRecovery28Seventh q a,
            riccatiHasBidegree_monomialUniformRecovery28Seventh q a,
            by intro u hu hper; rfl⟩
        · have hEpos : 0 < E q := by omega
          obtain ⟨v, hv, hvorder⟩ :=
            riccatiJet_exists_high_factor_of_positive_excessUniformRecovery28Seventh j q hEpos
          have hmv : q v = 1 :=
            riccatiJet_high_factor_multiplicity_eq_oneNativeRecovery
              hj q v hqcount hv hvorder
          let r : Jet →₀ ℕ := q - Finsupp.single v 1
          have hsplit : D r + v.2 = D q := by
            dsimp [r, D, riccatiJetDerivativeOrderWeightNativeRecovery]
            exact Finsupp.weight_sub_single_add
              (w := fun z : Jet => z.2) (Finsupp.mem_support_iff.mp hv)
          have hrbound : D r ≤ j - 2 := by omega
          have hresOrder : ∀ w ∈ r.support, w.2 ≤ j - 2 := by
            intro w hw
            have hcoord := riccatiJetDerivativeOrderWeight_coordinate_leNativeRecovery r w hw
            have hwpos : 0 < r w := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hw)
            dsimp [D, riccatiJetDerivativeOrderWeightNativeRecovery] at hcoord hrbound
            have hindex : w.2 ≤ r w * w.2 := by
              calc
                w.2 = 1 * w.2 := by simp
                _ ≤ r w * w.2 := Nat.mul_le_mul_right w.2 (by omega)
            exact le_trans hindex (le_trans hcoord hrbound)
          have hbranchExists : ∀ w ∈ r.support,
              ∃ Q : Poly,
                HasJetOrderAtMostNativeRecovery j Q ∧
                HasJetFactorDegreeOnSupportUniformRecovery28Seventh Q q.degree ∧
                HasRiccatiJetBidegreeAfterComponents Q
                  (riccatiJetBidegreeAfterComponents q) ∧
                ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
                  (hper : Function.Periodic u 1),
                  J u (riccatiIBPBranchExponentNativeRecovery28Second r v w)
                    (a * (r w : ℤ)) =
                    ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x Q := by
            intro w hw
            let n := riccatiIBPBranchExponentNativeRecovery28Second r v w
            have hDbranch : D n = D q := by
              dsimp [n, r, D, riccatiJetDerivativeOrderWeightNativeRecovery]
              exact riccatiJetDerivativeOrderWeight_rebalance_eqNativeRecoverySecond
                q v w hv hw (by omega)
            have hEbranch : E n < E q := by
              dsimp [n, r, E, riccatiJetDerivativeExcessNativeRecovery]
              exact riccatiJetDerivativeExcess_rebalance_strictly_decreasesNativeRecovery
                hj q v w hv hmv hvorder hw (hresOrder w hw)
            have hEne : E n < e := by rw [← he]; exact hEbranch
            have hrec := ih (E n) hEne n (a * (r w : ℤ)) rfl (by
              rw [hDbranch]
              exact hqcount)
            rcases hrec with ⟨Q, hQlow, hQdegree, hQbd, hQall⟩
            have hnDegree : n.degree = q.degree := by
              dsimp [n, r]
              exact riccatiJetIBPBranch_degree_eqNativeRecovery28Fourth q v w hv hw
            have hQdegree' :
                HasJetFactorDegreeOnSupportUniformRecovery28Seventh Q q.degree := by
              intro k hk
              calc
                k.degree = n.degree := hQdegree k hk
                _ = q.degree := hnDegree
            have hnBd :
                riccatiJetBidegreeAfterComponents n =
                  riccatiJetBidegreeAfterComponents q := by
              dsimp [n, r]
              exact riccatiJetIBPBranch_bidegree_eqNativeRecovery28Fourth
                q v w hv hw (by omega)
            refine ⟨Q, hQlow, hQdegree', ?_, hQall⟩
            rw [← hnBd]
            exact hQbd
          let Q : Jet → Poly := fun w =>
            if hw : w ∈ r.support then Classical.choose (hbranchExists w hw) else 0
          have hQlow : ∀ w ∈ r.support,
              HasJetOrderAtMostNativeRecovery j (Q w) := by
            intro w hw
            simp only [Q, dif_pos hw]
            exact (Classical.choose_spec (hbranchExists w hw)).1
          have hQdegree : ∀ w ∈ r.support,
              HasJetFactorDegreeOnSupportUniformRecovery28Seventh (Q w) q.degree := by
            intro w hw
            simp only [Q, dif_pos hw]
            exact (Classical.choose_spec (hbranchExists w hw)).2.1
          have hQbd : ∀ w ∈ r.support,
              HasRiccatiJetBidegreeAfterComponents (Q w)
                (riccatiJetBidegreeAfterComponents q) := by
            intro w hw
            simp only [Q, dif_pos hw]
            exact (Classical.choose_spec (hbranchExists w hw)).2.2.1
          let P : Poly := -(∑ w ∈ r.support, Q w)
          have hPlow : HasJetOrderAtMostNativeRecovery j P := by
            apply hasJetOrderAtMost_negNativeRecovery
            exact hasJetOrderAtMost_finset_sumNativeRecovery
              r.support Q hQlow
          have hPdegree :
              HasJetFactorDegreeOnSupportUniformRecovery28Seventh P q.degree := by
            apply riccatiHasFactorDegree_negUniformRecovery28Seventh
            exact riccatiHasFactorDegree_sumUniformRecovery28Seventh
              r.support Q hQdegree
          have hPbd : HasRiccatiJetBidegreeAfterComponents P
              (riccatiJetBidegreeAfterComponents q) := by
            apply riccatiHasBidegree_negUniformRecovery28Seventh
            exact riccatiHasBidegree_sumUniformRecovery28Seventh
              r.support Q hQbd
          have hnormalizedSum :
              ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
                (hper : Function.Periodic u 1),
              (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x P) =
                -∑ w ∈ r.support,
                  ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (Q w) := by
            intro u hu hper
            dsimp [P]
            calc
              (∫ x in (0 : ℝ)..1,
                  riccatiJetEvaluation u x (-(∑ w ∈ r.support, Q w))) =
                  ∫ x in (0 : ℝ)..1,
                    -(∑ w ∈ r.support, riccatiJetEvaluation u x (Q w)) := by
                      apply intervalIntegral.integral_congr
                      intro x hx
                      simp [riccatiJetEvaluation, polynomialEvaluation, map_neg, map_sum]
              _ = -(∫ x in (0 : ℝ)..1,
                    ∑ w ∈ r.support, riccatiJetEvaluation u x (Q w)) := by simp
              _ = -∑ w ∈ r.support,
                    ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (Q w) := by
                      congr 1
                      calc
                        (∫ x in (0 : ℝ)..1,
                            ∑ w ∈ r.support, riccatiJetEvaluation u x (Q w)) =
                            ∫ x in (0 : ℝ)..1,
                              riccatiJetEvaluation u x (∑ w ∈ r.support, Q w) := by
                                apply intervalIntegral.integral_congr
                                intro x hx
                                simp [riccatiJetEvaluation, polynomialEvaluation, map_sum]
                        _ = ∑ w ∈ r.support,
                            ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (Q w) :=
                              riccatiJetEvaluation_integral_finset_sumNativeRecoverySecond
                                u hu r.support Q
          have hbranchNorm :
              ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
                (hper : Function.Periodic u 1),
              -∑ w ∈ r.support,
                J u (riccatiIBPBranchExponentNativeRecovery28Second r v w)
                  (a * (r w : ℤ)) =
              -∑ w ∈ r.support,
                ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (Q w) := by
            intro u hu hper
            congr 1
            apply Finset.sum_congr rfl
            intro w hw
            dsimp only [Q]
            rw [dite_eq_left hw]
            exact (Classical.choose_spec (hbranchExists w hw)).2.2.2 u hu hper
          have hfinal :
              ∀ (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
                (hper : Function.Periodic u 1),
              J u q a = -∑ w ∈ r.support,
                J u (riccatiIBPBranchExponentNativeRecovery28Second r v w)
                  (a * (r w : ℤ)) := by
            intro u hu hper
            have hstep :=
              riccatiJetMonomial_periodic_ibp_finite_branchesNativeRecovery28Second
                u hu hper q a v hv (by omega)
            simpa [J, r] using hstep
          refine ⟨P, hPlow, hPdegree, hPbd, ?_⟩
          intro u hu hper
          calc
            J u q a = -∑ w ∈ r.support,
                J u (riccatiIBPBranchExponentNativeRecovery28Second r v w)
                  (a * (r w : ℤ)) := hfinal u hu hper
            _ = -∑ w ∈ r.support,
                ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (Q w) :=
                  hbranchNorm u hu hper
            _ = ∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x P :=
                  (hnormalizedSum u hu hper).symm
  exact hmain (E m) m c rfl hcount

end NlsGge.HierarchyRiccati.Core

end

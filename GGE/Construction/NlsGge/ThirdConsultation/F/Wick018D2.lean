import Mathlib
import NlsGge.ThirdConsultation.F.Round5
import NlsGge.ThirdConsultation.F.Wick018A
import NlsGge.ThirdConsultation.F.Wick018B
import NlsGge.ThirdConsultation.F.Wick018C
import NlsGge.ThirdConsultation.F.Wick018D1
import NlsGge.Hierarchy.RiccatiLocalRemainderSobolev38
import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38

                                                                                                           
                                                                                                               
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.Measure

namespace NlsGge.ThirdConsultation.F
attribute [local instance] Classical.propDecidable
namespace Wick018D2

/-- Derived (not assumed): every supported monomial of `R_j` has gauge zero. -/
theorem gauge_zero (j : ℕ) (q : Jet →₀ ℕ) (hq : q ∈ (normalizedRemainder38 j).support) :
    riccatiJetGaugeHomAfterComponents q = 0 := by
  have hprop := formalChargeRemainderNormalizedUniform_propertiesNativeRecovery29Fourth j
  have hbi := hprop.2.2.1 q hq
  simpa [riccatiJetBidegreeAfterComponents] using congrArg Prod.snd hbi

/-- Derived (not assumed): all occurrence orders are `≤ m - 1`. -/
theorem hord_of_support (m j : ℕ) (hj : j ≤ m) (q : Jet →₀ ℕ)
    (hq : q ∈ (normalizedRemainder38 j).support) : ∀ t : OccType38 q, occOrd38 q t ≤ m - 1 :=
  fun t => normalizedRemainder38_order m j hj q hq t.1.1 t.1.2

theorem card_filter_split {α : Type*} [Fintype α] [DecidableEq α] (R : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (Finset.univ.filter p).card = (R.filter p).card + ((Finset.univ \ R).filter p).card := by
  simp only [Finset.card_filter]
  rw [add_comm, Finset.sum_sdiff (Finset.subset_univ R)]

/-- W8: counting for `contractionPatterns`. -/
theorem pattern_counting (q : Jet →₀ ℕ) (hg : riccatiJetGaugeHomAfterComponents q = 0)
    (R : Finset (OccType38 q)) (hR : R ∈ contractionPatterns q) :
    ∃ k l : ℕ, 1 ≤ k ∧ (tailUnbar q R).card = k ∧ (tailBar q R).card = k ∧
      R.card = 2 * l ∧ q.degree = 2 * k + 2 * l := by
  obtain ⟨hne, hcard⟩ := (Finset.mem_filter.1 hR).2
  have hb := card_bar_occ38 q hg
  have hs1 := card_filter_split R (fun t : OccType38 q => occBar38 q t = true)
  have hs2 := card_filter_split R (fun t : OccType38 q => ¬ occBar38 q t = true)
  have hU : (Finset.univ \ R).filter (fun t : OccType38 q => ¬ occBar38 q t = true) = tailUnbar q R :=
    Wick018B.filter_unbar q R
  have hB : (Finset.univ \ R).filter (fun t : OccType38 q => occBar38 q t = true) = tailBar q R :=
    Wick018B.filter_bar q R
  rw [hU] at hs2
  rw [hB] at hs1
  have hRc := Finset.card_filter_add_card_filter_not (s := R) (fun t : OccType38 q => occBar38 q t = true)
  have hdeg : q.degree = (Finset.univ : Finset (OccType38 q)).card := by
    rw [Finset.card_univ, card_occ38]
  have hdeg2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (OccType38 q)))
    (fun t : OccType38 q => occBar38 q t = true)
  have hlt : R.card < (Finset.univ : Finset (OccType38 q)).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ R, hne⟩)
  rw [hs1, hs2] at hb
  rw [hs1, hs2] at hdeg2
  refine ⟨(tailUnbar q R).card, (R.filter fun t => occBar38 q t = true).card, ?_, rfl, hcard.symm, ?_, ?_⟩
  · omega
  · omega
  · omega

theorem wickMatchingSum_univ (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (q : Jet →₀ ℕ) :
    wickMatchingSum m β N q Finset.univ = 1 := by
  have hU : tailUnbar q (Finset.univ : Finset (OccType38 q)) = ∅ := by
    unfold tailUnbar; simp
  have hB : tailBar q (Finset.univ : Finset (OccType38 q)) = ∅ := by
    unfold tailBar; simp
  unfold wickMatchingSum
  rw [hU, hB]
  simp

/-- The full-cutoff monomial expansion at the tail limit. -/
theorem sum_powerset_expectation (m : ℕ) (β : ℕ → ℝ) (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)
    (j : ℕ) (hj : j ≤ m) (q : Jet →₀ ℕ) (hqs : q ∈ (normalizedRemainder38 j).support)
    (N : ℕ) (hN : 1 ≤ N) (z : FourierPlane N) :
    ∫ s, localRemainderMonomialValue38 m j q
        (toCarrier38 _ (planeElement38 ((m - 1 : ℕ) : ℝ) N z + tailRealization38 m N s))
        ∂gammaM38 m β =
      ∑ R ∈ (Finset.univ : Finset (OccType38 q)).powerset,
        (((normalizedRemainder38 j).coeff q : ℂ) *
          ∫ x in (0 : ℝ)..1,
            (∏ i ∈ R, jet38 (occBar38 q) (occOrd38 q) (planeReal N z) i x) *
              wickMatchingSum m β N q R).re := by
  have hq := F016L5.rate_pos' m hm β hβ
  have hβ0 : ∀ i ≤ m, 0 ≤ β i := fun i hi => (hβ i hi).le
  obtain ⟨-, htend⟩ := Wick018C.tendsto_integral_monomial m β hm hβ0 (hβ 0 (Nat.zero_le _))
    (hβ m le_rfl) j q N (planeElement38 ((m - 1 : ℕ) : ℝ) N z)
  simp only [Wick018D1.finite_cutoff_expectation m β hm hq j hj q hqs N z] at htend
  have hord := hord_of_support m j hj q hqs
  set c : ℂ := ((normalizedRemainder38 j).coeff q : ℂ)
  have h2 : Tendsto (fun N' : ℕ => ∑ R ∈ (Finset.univ : Finset (OccType38 q)).powerset,
      (c * ∫ x in (0 : ℝ)..1,
        (∏ i ∈ R, jet38 (occBar38 q) (occOrd38 q) (planeReal N z) i x) *
          Wick018B.wickMatchingSumFin m β N N' q R).re) atTop
      (𝓝 (∑ R ∈ (Finset.univ : Finset (OccType38 q)).powerset,
        (c * ∫ x in (0 : ℝ)..1,
          (∏ i ∈ R, jet38 (occBar38 q) (occOrd38 q) (planeReal N z) i x) *
            wickMatchingSum m β N q R).re)) := by
    refine tendsto_finset_sum _ (fun R _ => ?_)
    simp only [intervalIntegral.integral_mul_const]
    exact (Complex.continuous_re.comp (continuous_const.mul
      (continuous_const.mul continuous_id))).continuousAt.tendsto.comp
      (Wick018C.tendsto_wickMatchingSumFin m hm β hβ N hN q hord R)
  exact tendsto_nhds_unique htend h2

/-- The tail-limit expansion: expectation minus the plane value is the sum over contraction patterns. -/
theorem expectation_tail (m : ℕ) (β : ℕ → ℝ) (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)
    (j : ℕ) (hj : j ≤ m) (q : Jet →₀ ℕ) (hqs : q ∈ (normalizedRemainder38 j).support)
    (N : ℕ) (hN : 1 ≤ N) (z : FourierPlane N) :
    (∫ s, localRemainderMonomialValue38 m j q
        (toCarrier38 _ (planeElement38 ((m - 1 : ℕ) : ℝ) N z + tailRealization38 m N s))
        ∂gammaM38 m β) -
      localRemainderMonomialValue38 m j q
        (toCarrier38 _ (planeElement38 ((m - 1 : ℕ) : ℝ) N z)) =
      ∑ R ∈ contractionPatterns q, contractedMonomial m β N j z q R := by
  rw [sum_powerset_expectation m β hm hβ j hj q hqs N hN z,
    ← Finset.add_sum_erase _ _ (Finset.mem_powerset.2 (Finset.subset_univ (Finset.univ : Finset (OccType38 q)))),
    Wick018D1.mon_plane m hm N z j hj q hqs, wickMatchingSum_univ]
  simp only [mul_one]
  rw [add_sub_cancel_left]
  have hset : contractionPatterns q =
      ((Finset.univ : Finset (OccType38 q)).powerset.erase Finset.univ).filter
        (fun R => (tailUnbar q R).card = (tailBar q R).card) := by
    ext R
    simp only [contractionPatterns, Finset.mem_filter, Finset.mem_erase, Finset.mem_powerset,
      Finset.subset_univ, and_true]
    tauto
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun R _ => ?_
  unfold contractedMonomial
  split_ifs with h
  · rfl
  · rw [Wick018C.wickMatchingSum_eq_zero_of_card_ne m β N q R h]
    simp

end Wick018D2
end NlsGge.ThirdConsultation.F
end

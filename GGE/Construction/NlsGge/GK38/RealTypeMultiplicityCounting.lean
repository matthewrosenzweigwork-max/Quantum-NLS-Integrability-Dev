import NlsGge.GK38.RealTypeMultiplicityWitnesses

/-! # S6: exhausting actual critical root multisets

Distinct real witnesses saturate the central count and each far singleton count.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem counting_nodup_order_one38 {f : ℂ → ℂ} {q N : ℕ}
    (h : RootCountingAt38 f q N) (c : ℂ) (r : ℝ)
    (hn : (Lib.zeroMultiset f (ball c r)).Nodup) {z : ℂ}
    (hz : z ∈ Lib.zeroMultiset f (ball c r)) : analyticOrderAt f z = 1 := by
  classical
  have hm := (counting_mem_zeroMultiset38 h c r z).mp hz
  have hc := Multiset.count_eq_one_of_mem hn hz
  rw [Lib.count_zeroMultiset_ball (h.2.1.mono (subset_univ _)), ite_eq_left hm.1] at hc
  rw [← Nat.cast_analyticOrderNatAt (counting_order_ne_top38 h z), hc]
  rfl

theorem critical_central_saturation38 (f : ℂ → ℂ) (N : ℕ) (ν : ℤ → ℂ)
    (h : RootCountingAt38 f 1 N) (hi : Function.Injective ν)
    (hv : ∀ n : ℤ, n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) →
      ν n ∈ ball (0 : ℂ) (countingRadius38 N) ∧ f (ν n) = 0) :
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).val.map ν =
      Lib.zeroMultiset f (ball (0 : ℂ) (countingRadius38 N)) ∧
    ∀ n : ℤ, n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) → analyticOrderAt f (ν n) = 1 := by
  classical
  let s := (Finset.Icc (-(N : ℤ)) (N : ℤ)).val.map ν
  have hn : s.Nodup := (Finset.Icc (-(N : ℤ)) (N : ℤ)).nodup.map hi
  have hs : s ≤ Lib.zeroMultiset f (ball (0 : ℂ) (countingRadius38 N)) := by
    apply (Multiset.le_iff_subset hn).mpr
    intro z hz
    obtain ⟨n, hmem, rfl⟩ := Multiset.mem_map.mp hz
    exact (counting_mem_zeroMultiset38 h _ _ _).mpr (hv n hmem)
  have hc : s.card = 2 * N + 1 := by
    simp only [s, Multiset.card_map, Finset.card_val, Int.card_Icc]
    omega
  have he : s = Lib.zeroMultiset f (ball (0 : ℂ) (countingRadius38 N)) :=
    Multiset.eq_of_le_of_card_le hs (by rw [hc, h.2.2.2.2.2.1]; simp)
  refine ⟨he, fun n hn' => ?_⟩
  apply counting_nodup_order_one38 h _ _ (he ▸ hn)
  exact (counting_mem_zeroMultiset38 h _ _ _).mpr (hv n hn')

theorem critical_far_saturation38 (f : ℂ → ℂ) (N : ℕ) (ν : ℤ → ℂ)
    (h : RootCountingAt38 f 1 N)
    (hv : ∀ n : ℤ, (N : ℤ) < |n| →
      ν n ∈ ball (countingCenter38 n) (Real.pi / 4) ∧ f (ν n) = 0) :
    ∀ n : ℤ, (N : ℤ) < |n| →
      ({ν n} : Multiset ℂ) = Lib.zeroMultiset f (ball (countingCenter38 n) (Real.pi / 4)) ∧
      analyticOrderAt f (ν n) = 1 := by
  classical
  intro n hn
  have hm := (counting_mem_zeroMultiset38 h _ _ _).mpr (hv n hn)
  obtain ⟨w, hw⟩ := Multiset.card_eq_one.mp (h.2.2.2.2.1 n hn)
  have he : ν n = w := by simpa only [hw, Multiset.mem_singleton] using hm
  have hs : ({ν n} : Multiset ℂ) = Lib.zeroMultiset f (ball (countingCenter38 n) (Real.pi / 4)) := by
    rw [hw, he]
  exact ⟨hs, counting_nodup_order_one38 h _ _ (hs ▸ Multiset.nodup_singleton _) hm⟩

theorem realInterval_mem_ball38 (a b x c r : ℝ) (hx : x ∈ Icc a b)
    (ha : (a : ℂ) ∈ ball (c : ℂ) r) (hb : (b : ℂ) ∈ ball (c : ℂ) r) :
    (x : ℂ) ∈ ball (c : ℂ) r := by
  simp only [mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq, abs_lt] at ha hb ⊢
  constructor <;> linarith [hx.1, hx.2]

theorem gap_endpoint_central_mem38 (u : PhysicalL2) {N : ℕ}
    (h : RootCountingAt38 (perChar (realSlice u)) 2 N) {n : ℤ} (hn : |n| ≤ (N : ℤ)) :
    (actualGapLowerAllE02_38 u n : ℂ) ∈ ball (0 : ℂ) (countingRadius38 N) ∧
    (actualGapUpperAllE02_38 u n : ℂ) ∈ ball (0 : ℂ) (countingRadius38 N) := by
  have hb := abs_le.mp hn
  rw [← (lamPlus_real u n).2, ← (lamPlus_real u n).1]
  change lamSeq (realSlice u) (2 * n) ∈ _ ∧ lamSeq (realSlice u) (2 * n + 1) ∈ _
  rw [lamSeq_eq_candidate38 _ h]
  constructor <;> apply periodicCandidate_central_mem38 h <;>
    change -(2 * (N : ℤ)) ≤ _ ∧ _ ≤ 2 * (N : ℤ) + 1 <;> omega

theorem gap_endpoint_far_mem38 (u : PhysicalL2) {N : ℕ}
    (h : RootCountingAt38 (perChar (realSlice u)) 2 N) {n : ℤ} (hn : (N : ℤ) < |n|) :
    (actualGapLowerAllE02_38 u n : ℂ) ∈ ball (countingCenter38 n) (Real.pi / 4) ∧
    (actualGapUpperAllE02_38 u n : ℂ) ∈ ball (countingCenter38 n) (Real.pi / 4) := by
  have hb : ¬ (-(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) := fun hb => (not_le.mpr hn) (abs_le.mpr hb)
  rw [← (lamPlus_real u n).2, ← (lamPlus_real u n).1]
  change lamSeq (realSlice u) (2 * n) ∈ _ ∧ lamSeq (realSlice u) (2 * n + 1) ∈ _
  rw [lamSeq_eq_candidate38 _ h]
  have hm : ¬ periodicCentralIndex38 N (2 * n) := by unfold periodicCentralIndex38; omega
  have hp : ¬ periodicCentralIndex38 N (2 * n + 1) := by unfold periodicCentralIndex38; omega
  exact ⟨by simpa only [(periodic_index_pair38 n).1] using periodicCandidate_far_mem38 h hm,
    by simpa only [(periodic_index_pair38 n).2.1] using periodicCandidate_far_mem38 h hp⟩

theorem gap_critical_localization38 (u : PhysicalL2) (N : ℕ) (ν : ℤ → ℝ)
    (hp : RootCountingAt38 (perChar (realSlice u)) 2 N)
    (_hd : RootCountingAt38 (deriv (discrim (realSlice u))) 1 N)
    (hv : ∀ n : ℤ, ν n ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) ∧
      deriv (discrim (realSlice u)) (ν n : ℂ) = 0) :
    StrictMono ν ∧
    (∀ n : ℤ, |n| ≤ (N : ℤ) → (ν n : ℂ) ∈ ball (0 : ℂ) (countingRadius38 N)) ∧
    (∀ n : ℤ, (N : ℤ) < |n| → (ν n : ℂ) ∈ ball (countingCenter38 n) (Real.pi / 4)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m n hmn
    exact (hv m).1.2.trans_lt ((gap_indices_separated38 u hmn).trans_le (hv n).1.1)
  · intro n hn
    obtain ⟨hl, hu⟩ := gap_endpoint_central_mem38 u hp hn
    exact realInterval_mem_ball38 _ _ _ 0 _ (hv n).1 hl hu
  · intro n hn
    obtain ⟨hl, hu⟩ := gap_endpoint_far_mem38 u hp hn
    simp only [countingCenter38, ← Complex.ofReal_intCast, ← Complex.ofReal_mul] at hl hu ⊢
    exact realInterval_mem_ball38 _ _ _ ((n : ℝ) * Real.pi) _ (hv n).1 hl hu

end
end NlsGge.GK38

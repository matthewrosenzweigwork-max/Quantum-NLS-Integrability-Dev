import NlsGge.GK38.IsolatingGeometry
import NlsGge.GK38.RealTypeSpectrumSorting

/-! Finite saturation and horizontal projection for complex root multisets. -/
set_option autoImplicit false
open Set Metric
open Classical
namespace NlsGge.GK38
noncomputable section

theorem isolating_central_coverage38 {f : ℂ → ℂ} {q N : ℕ}
    (hN : RootCountingAt38 f q N) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ)
    (hg : IsolatingGeometry38 C R c N)
    (hsub : ∀ n : ℤ, |n| ≤ (N : ℤ) → ball (C n) (R n) ⊆ ball 0 (countingRadius38 N))
    (hc : ∀ n : ℤ, |n| ≤ (N : ℤ) → (Lib.zeroMultiset f (ball (C n) (R n))).card = q) :
    ∀ z ∈ Lib.zeroMultiset f (ball 0 (countingRadius38 N)),
      ∃ n : ℤ, |n| ≤ (N : ℤ) ∧ z ∈ ball (C n) (R n) := by
  classical
  let S := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let D : Set ℂ := ⋃ n ∈ S, ball (C n) (R n)
  have hD : D ⊆ ball 0 (countingRadius38 N) := by
    intro z hz
    obtain ⟨n, hn, hz⟩ := mem_iUnion₂.mp hz
    exact hsub n (abs_le.mpr (Finset.mem_Icc.mp hn)) hz
  have hd : (S : Set ℤ).PairwiseDisjoint (fun n => ball (C n) (R n)) := by
    intro m hm n hn hmn
    exact isolating_geometry_disjoint38 C R c N hg hmn
  have hcard : (Lib.zeroMultiset f D).card = q * (2 * N + 1) := by
    rw [Lib.card_zeroMultiset_biUnion (hN.2.1.mono (subset_univ _))
      (isCompact_closedBall (0 : ℂ) (countingRadius38 N)) S (fun n => ball (C n) (R n))
      (fun n hn => (hsub n (abs_le.mpr (Finset.mem_Icc.mp hn))).trans ball_subset_closedBall) hd]
    rw [Finset.sum_congr rfl (fun n hn => hc n (abs_le.mpr (Finset.mem_Icc.mp hn)))]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hs : S.card = 2 * N + 1 := by simp [S, Int.card_Icc]; omega
    rw [hs, Nat.mul_comm]
    norm_cast
  have hle : Lib.zeroMultiset f D ≤ Lib.zeroMultiset f (ball 0 (countingRadius38 N)) := by
    apply Multiset.le_iff_count.mpr
    intro z
    rw [Lib.count_zeroMultiset_of_subset (hN.2.1.mono (subset_univ _))
      (isCompact_closedBall (0 : ℂ) (countingRadius38 N)) (hD.trans ball_subset_closedBall),
      Lib.count_zeroMultiset_ball (hN.2.1.mono (subset_univ _))]
    by_cases hz : z ∈ D
    · simp [hz, hD hz]
    · simp [hz]
  have he : Lib.zeroMultiset f D = Lib.zeroMultiset f (ball 0 (countingRadius38 N)) := by
    apply Multiset.eq_of_le_of_card_le hle
    rw [hcard, hN.2.2.2.2.2.1]
  intro z hz
  rw [← he] at hz
  have hzD := ((Lib.mem_zeroMultiset (hN.2.1.mono (subset_univ _))
    (isCompact_closedBall (0 : ℂ) (countingRadius38 N)) (hD.trans ball_subset_closedBall)).mp hz).1
  obtain ⟨n, hn, hz⟩ := mem_iUnion₂.mp hzD
  exact ⟨n, abs_le.mpr (Finset.mem_Icc.mp hn), hz⟩

def isolatingProjection38 (C : ℤ → ℂ) (R : ℤ → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  if h : ∃ n : ℤ, |n| ≤ (N : ℤ) ∧ z ∈ ball (C n) (R n) then
    countingCenter38 (Classical.choose h) else 0

theorem isolating_projection_eq38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) {n : ℤ} (hn : |n| ≤ (N : ℤ))
    {z : ℂ} (hz : z ∈ ball (C n) (R n)) :
    isolatingProjection38 C R N z = countingCenter38 n := by
  classical
  have he : ∃ m : ℤ, |m| ≤ (N : ℤ) ∧ z ∈ ball (C m) (R m) := ⟨n, hn, hz⟩
  rw [isolatingProjection38, dite_eq_left he]
  congr 1
  by_contra hne
  exact Set.disjoint_left.mp (isolating_geometry_disjoint38 C R c N hg hne)
    (Classical.choose_spec he).2 hz

theorem isolating_central_filter38 {f : ℂ → ℂ} {q N : ℕ} (hN : RootCountingAt38 f q N)
    {a : ℂ} {r : ℝ} (hsub : ball a r ⊆ ball 0 (countingRadius38 N)) :
    (Lib.zeroMultiset f (ball 0 (countingRadius38 N))).filter (fun z => z ∈ ball a r) =
      Lib.zeroMultiset f (ball a r) := by
  classical
  apply Multiset.ext'
  intro z
  rw [Multiset.count_filter, Lib.count_zeroMultiset_ball (hN.2.1.mono (subset_univ _)),
    Lib.count_zeroMultiset_ball (hN.2.1.mono (subset_univ _))]
  by_cases hz : z ∈ ball a r
  · simp [hz, hsub hz]
  · simp [hz]

theorem isolating_projection_mono38 {f : ℂ → ℂ} {q N : ℕ} (_hN : RootCountingAt38 f q N)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (hg : IsolatingGeometry38 C R c N)
    (hcov : ∀ z ∈ Lib.zeroMultiset f (ball 0 (countingRadius38 N)),
      ∃ n : ℤ, |n| ≤ (N : ℤ) ∧ z ∈ ball (C n) (R n)) :
    ∀ z ∈ Lib.zeroMultiset f (ball 0 (countingRadius38 N)),
    ∀ w ∈ Lib.zeroMultiset f (ball 0 (countingRadius38 N)), complexLexLE38 z w →
      complexLexLE38 (isolatingProjection38 C R N z) (isolatingProjection38 C R N w) := by
  intro z hz w hw hzw
  obtain ⟨m, hm, hzm⟩ := hcov z hz
  obtain ⟨n, hn, hwn⟩ := hcov w hw
  rw [isolating_projection_eq38 C R c N hg hm hzm, isolating_projection_eq38 C R c N hg hn hwn]
  apply countingCenter_lex_mono38
  by_contra hmn
  have hr := isolating_horizontal_order38 C R c N hg (lt_of_not_ge hmn) hwn hzm
  rcases (complexLexLE_iff38 z w).mp hzw with h | h
  · linarith
  · linarith [h.1]

theorem isolating_projection_map38 {f : ℂ → ℂ} {q N : ℕ} (hN : RootCountingAt38 f q N)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (hg : IsolatingGeometry38 C R c N)
    (hsub : ∀ n : ℤ, |n| ≤ (N : ℤ) → ball (C n) (R n) ⊆ ball 0 (countingRadius38 N))
    (hc : ∀ n : ℤ, |n| ≤ (N : ℤ) → (Lib.zeroMultiset f (ball (C n) (R n))).card = q)
    (s : Multiset ℂ)
    (hs : ∀ n : ℤ, |n| ≤ (N : ℤ) → s.count (countingCenter38 n) = q)
    (hscov : ∀ a ∈ s, ∃ n : ℤ, |n| ≤ (N : ℤ) ∧ a = countingCenter38 n) :
    (Lib.zeroMultiset f (ball 0 (countingRadius38 N))).map (isolatingProjection38 C R N) = s := by
  let M := Lib.zeroMultiset f (ball 0 (countingRadius38 N))
  have hcov := isolating_central_coverage38 hN C R c hg hsub hc
  apply Multiset.ext'
  intro a
  by_cases ha : ∃ n : ℤ, |n| ≤ (N : ℤ) ∧ a = countingCenter38 n
  · obtain ⟨n, hn, rfl⟩ := ha
    have hefilter : M.filter (fun z => countingCenter38 n = isolatingProjection38 C R N z) =
        M.filter (fun z => z ∈ ball (C n) (R n)) := by
      apply Multiset.filter_congr
      intro z hz
      obtain ⟨m, hm, hzm⟩ := hcov z hz
      rw [isolating_projection_eq38 C R c N hg hm hzm]
      constructor
      · intro he
        have hnm := countingCenter_injective38 he
        simpa only [hnm] using hzm
      · intro hzn
        have he := isolating_projection_eq38 C R c N hg hn hzn
        rw [isolating_projection_eq38 C R c N hg hm hzm] at he
        exact he.symm
    rw [Multiset.count_map, hefilter, isolating_central_filter38 hN (hsub n hn), hc n hn, hs n hn]
  · have hnot : a ∉ s := fun h => ha (hscov a h)
    rw [Multiset.count_map, Multiset.count_eq_zero.mpr hnot]
    apply Multiset.card_eq_zero.mpr
    apply Multiset.filter_eq_nil.mpr
    intro z hz he
    obtain ⟨n, hn, hzn⟩ := hcov z hz
    exact ha ⟨n, hn, he.trans (isolating_projection_eq38 C R c N hg hn hzn)⟩

end
end NlsGge.GK38

import NlsGge.GK38.PeriodicLabellingRoots
import NlsGge.GK38.PeriodicLabellingGeometry
import NlsGge.GK38.PeriodicLabellingRadius

/-! # S2: exact central multiset decomposition at larger cutoffs -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem counting_small_subset_central38 {M : ℕ} {n : ℤ} (hn : |n| ≤ (M : ℤ)) :
    ball (countingCenter38 n) (Real.pi / 4) ⊆ ball (0 : ℂ) (countingRadius38 M) := by
  intro z hz
  have hc := countingCenter_low_norm38 hn
  have hz' := mem_ball_iff_norm.mp hz
  have ht : ‖z‖ ≤ ‖z - countingCenter38 n‖ + ‖countingCenter38 n‖ := by
    simpa only [sub_add_cancel] using norm_add_le (z - countingCenter38 n) (countingCenter38 n)
  rw [mem_ball, dist_zero_right]
  unfold countingRadius38
  linarith

def interveningDiscs38 (N M : ℕ) : Finset ℤ :=
  (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter fun n => (N : ℤ) < |n|

theorem mem_interveningDiscs38 {N M : ℕ} {n : ℤ} :
    n ∈ interveningDiscs38 N M ↔ |n| ≤ (M : ℤ) ∧ (N : ℤ) < |n| := by
  simp only [interveningDiscs38, Finset.mem_filter, Finset.mem_Icc, ← abs_le]

theorem count_finset_sum38 {ι : Type*} (s : Finset ι) (F : ι → Multiset ℂ) (z : ℂ) :
    (∑ i ∈ s, F i).count z = ∑ i ∈ s, (F i).count z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, Multiset.count_add]

/-- Exhaustive coverage at N accounts for every zero in the larger central disc. -/
theorem central_multiset_decomposition38 {f : ℂ → ℂ} {q N M : ℕ}
    (h : RootCountingAt38 f q N) (hNM : N ≤ M) :
    Lib.zeroMultiset f (ball (0 : ℂ) (countingRadius38 M)) =
      Lib.zeroMultiset f (ball (0 : ℂ) (countingRadius38 N)) +
        ∑ n ∈ interveningDiscs38 N M,
          Lib.zeroMultiset f (ball (countingCenter38 n) (Real.pi / 4)) := by
  classical
  have ha := h.2.1
  have hsub : ball (0 : ℂ) (countingRadius38 N) ⊆ ball 0 (countingRadius38 M) :=
    ball_subset_ball (countingRadius_mono38 hNM)
  refine Multiset.ext' fun z => ?_
  rw [Multiset.count_add, count_finset_sum38]
  simp only [Lib.count_zeroMultiset_ball (ha.mono (subset_univ _))]
  by_cases hf : f z = 0
  · obtain hzN | ⟨n, hn, hzn⟩ := h.2.2.2.2.2.2 z hf
    · have hzM := hsub hzN
      rw [ite_eq_left hzM, ite_eq_left hzN]
      have hs : (∑ n ∈ interveningDiscs38 N M,
          if z ∈ ball (countingCenter38 n) (Real.pi / 4) then analyticOrderNatAt f z else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        rw [ite_eq_right]
        exact fun hz => (Set.disjoint_left.mp
          (counting_central_small_disjoint38 (mem_interveningDiscs38.mp hn).2)) hzN hz
      rw [hs, add_zero]
    · have hzN : z ∉ ball (0 : ℂ) (countingRadius38 N) := fun hz =>
        (Set.disjoint_left.mp (counting_central_small_disjoint38 hn)) hz hzn
      rw [ite_eq_right hzN, zero_add]
      by_cases hnM : |n| ≤ (M : ℤ)
      · have hnS := mem_interveningDiscs38.mpr ⟨hnM, hn⟩
        have hzM := counting_small_subset_central38 hnM hzn
        rw [ite_eq_left hzM]
        symm
        rw [Finset.sum_eq_single n]
        · rw [ite_eq_left hzn]
        · intro m _ hmn
          rw [ite_eq_right]
          exact fun hzm => (Set.disjoint_left.mp (counting_small_ball_disjoint38 hmn)) hzm hzn
        · intro hnnot
          exact (hnnot hnS).elim
      · have hnM' : (M : ℤ) < |n| := lt_of_not_ge hnM
        have hzM : z ∉ ball (0 : ℂ) (countingRadius38 M) := fun hz =>
          (Set.disjoint_left.mp (counting_central_small_disjoint38 hnM')) hz hzn
        rw [ite_eq_right hzM]
        symm
        apply Finset.sum_eq_zero
        intro m hm
        rw [ite_eq_right]
        have hmn : m ≠ n := by
          intro he
          apply hnM
          simpa only [he] using (mem_interveningDiscs38.mp hm).1
        exact fun hzm => (Set.disjoint_left.mp (counting_small_ball_disjoint38 hmn)) hzm hzn
  · have hord : analyticOrderNatAt f z = 0 := by
      have he := (ha z (mem_univ z)).analyticOrderAt_eq_zero.mpr hf
      simp [analyticOrderNatAt, he]
    simp [hord]

end
end NlsGge.GK38

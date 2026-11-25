import NlsGge.GK38.PeriodicLabellingEnumeration
import NlsGge.GK38.PeriodicLabellingOrder
import NlsGge.GK38.PeriodicLabellingDecomposition

/-! # S2: larger central windows contain exactly the larger central multiset -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem periodicCandidate_mem_larger38 {f : ℂ → ℂ} {N M : ℕ}
    (h : RootCountingAt38 f 2 N) (hNM : N ≤ M) (k : ℤ) :
    periodicCandidate38 f N k ∈ ball (0 : ℂ) (countingRadius38 M) ↔ periodicCentralIndex38 M k := by
  by_cases hk : periodicCentralIndex38 N k
  · have hm := ball_subset_ball (countingRadius_mono38 hNM) (periodicCandidate_central_mem38 h hk)
    have hM : periodicCentralIndex38 M k := by
      unfold periodicCentralIndex38 at *
      omega
    exact iff_of_true hm hM
  · have hm := periodicCandidate_far_mem38 h hk
    by_cases hq : |k / 2| ≤ (M : ℤ)
    · have hmem := counting_small_subset_central38 hq hm
      have hM : periodicCentralIndex38 M k := by
        have hb := abs_le.mp hq
        unfold periodicCentralIndex38
        omega
      exact iff_of_true hmem hM
    · have hnot : periodicCandidate38 f N k ∉ ball (0 : ℂ) (countingRadius38 M) := fun hz =>
        (Set.disjoint_left.mp (counting_central_small_disjoint38 (lt_of_not_ge hq))) hz hm
      have hM : ¬ periodicCentralIndex38 M k := by
        intro hM
        unfold periodicCentralIndex38 at hM
        apply hq
        apply abs_le.mpr
        omega
      exact iff_of_false hnot hM

theorem criticalCandidate_mem_larger38 {f : ℂ → ℂ} {N M : ℕ}
    (h : RootCountingAt38 f 1 N) (hNM : N ≤ M) (k : ℤ) :
    criticalCandidate38 f N k ∈ ball (0 : ℂ) (countingRadius38 M) ↔ criticalCentralIndex38 M k := by
  by_cases hk : criticalCentralIndex38 N k
  · have hm := ball_subset_ball (countingRadius_mono38 hNM) (criticalCandidate_central_mem38 h hk)
    have hM : criticalCentralIndex38 M k := by
      unfold criticalCentralIndex38 at *
      omega
    exact iff_of_true hm hM
  · have hm := criticalCandidate_far_mem38 h hk
    by_cases hq : |k| ≤ (M : ℤ)
    · exact iff_of_true (counting_small_subset_central38 hq hm) (abs_le.mp hq)
    · have hnot : criticalCandidate38 f N k ∉ ball (0 : ℂ) (countingRadius38 M) := fun hz =>
        (Set.disjoint_left.mp (counting_central_small_disjoint38 (lt_of_not_ge hq))) hz hm
      have hM : ¬ criticalCentralIndex38 M k := fun hM => hq (abs_le.mpr hM)
      exact iff_of_false hnot hM

/-- Exact global occurrences determine a finite disc multiset when membership fixes the window. -/
theorem rootEnumeration_window_multiset38 {f : ℂ → ℂ} {q N : ℕ}
    (h : RootCountingAt38 f q N) {L : ℤ → ℂ} (he : RootEnumeration38 f L)
    (S : Finset ℤ) (c : ℂ) (r : ℝ) (hwindow : ∀ k : ℤ, L k ∈ ball c r ↔ k ∈ S) :
    S.val.map L = Lib.zeroMultiset f (ball c r) := by
  classical
  refine Multiset.ext' fun z => ?_
  rw [Lib.count_zeroMultiset_ball (h.2.1.mono (subset_univ _))]
  by_cases hz : z ∈ ball c r
  · rw [ite_eq_left hz]
    have hs : ∀ k : ℤ, L k = z → k ∈ S := by
      intro k hk
      apply (hwindow k).mp
      simpa only [hk] using hz
    have hc := (finite_occurrence_count38 L z S hs).2
    rw [(he.2.2 z).2, ← Nat.cast_analyticOrderNatAt (counting_order_ne_top38 h z)] at hc
    exact_mod_cast hc.symm
  · rw [ite_eq_right hz, Multiset.count_eq_zero_of_notMem]
    intro hm
    obtain ⟨k, hk, hval⟩ := Multiset.mem_map.mp hm
    apply hz
    rw [← hval]
    exact (hwindow k).mpr hk

theorem periodicCandidate_larger_multiset38 {f : ℂ → ℂ} {N M : ℕ}
    (h : RootCountingAt38 f 2 N) (hNM : N ≤ M) :
    (Finset.Icc (-(2 * (M : ℤ))) (2 * (M : ℤ) + 1)).val.map (periodicCandidate38 f N) =
      Lib.zeroMultiset f (ball (0 : ℂ) (countingRadius38 M)) := by
  apply rootEnumeration_window_multiset38 h (periodicCandidate_enumeration38 h)
  intro k
  exact (periodicCandidate_mem_larger38 h hNM k).trans Finset.mem_Icc.symm

theorem criticalCandidate_larger_multiset38 {f : ℂ → ℂ} {N M : ℕ}
    (h : RootCountingAt38 f 1 N) (hNM : N ≤ M) :
    (Finset.Icc (-(M : ℤ)) (M : ℤ)).val.map (criticalCandidate38 f N) =
      Lib.zeroMultiset f (ball (0 : ℂ) (countingRadius38 M)) := by
  apply rootEnumeration_window_multiset38 h (criticalCandidate_enumeration38 h)
  intro k
  exact (criticalCandidate_mem_larger38 h hNM k).trans Finset.mem_Icc.symm

end
end NlsGge.GK38

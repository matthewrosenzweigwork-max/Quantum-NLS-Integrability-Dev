import NlsGge.GK38.IsolatingProjection
import NlsGge.GK38.PeriodicLabellingFreeLabels

/-! Projection onto free central occurrences fixes the existing sorted indices. -/
set_option autoImplicit false
open Set Metric Classical
namespace NlsGge.GK38
noncomputable section

theorem isolating_free_count38 (N : ℕ) (n : ℤ) (hn : |n| ≤ (N : ℤ)) :
    (Lib.zeroMultiset (perChar 0) (ball 0 (countingRadius38 N))).count (countingCenter38 n) = 2 ∧
    (Lib.zeroMultiset (deriv (discrim 0)) (ball 0 (countingRadius38 N))).count (countingCenter38 n) = 1 := by
  have hz := (countingCenter_mem_central_iff38 N n).mpr hn
  have hs : Complex.sin (countingCenter38 n) = 0 := Complex.sin_eq_zero_iff.mpr ⟨n, rfl⟩
  constructor
  · rw [Lib.count_zeroMultiset_ball ((analyticOnNhd_perChar_z 0).mono (subset_univ _)),
      counting_free_order38]
    simp [hz, hs]
  · rw [Lib.count_zeroMultiset_ball ((analyticOnNhd_discrimDeriv38 0).mono (subset_univ _)),
      critical_free_order38]
    simp [hz, hs]

theorem isolating_free_support38 (N : ℕ) (z : ℂ)
    (hz : z ∈ Lib.zeroMultiset (perChar 0) (ball 0 (countingRadius38 N)) ∨
      z ∈ Lib.zeroMultiset (deriv (discrim 0)) (ball 0 (countingRadius38 N))) :
    ∃ n : ℤ, |n| ≤ (N : ℤ) ∧ z = countingCenter38 n := by
  have h : z ∈ ball 0 (countingRadius38 N) ∧ Complex.sin z = 0 := by
    rcases hz with hz | hz
    · have hh := (counting_mem_zeroMultiset38 (free_periodic_counting38 (N := 1) (by norm_num)) _ _ z).mp hz
      exact ⟨hh.1, (counting_free_zero_iff38 z).mp hh.2⟩
    · have hh := (counting_mem_zeroMultiset38 (free_critical_counting38 (N := 1) (by norm_num)) _ _ z).mp hz
      exact ⟨hh.1, (critical_free_zero_iff38 z).mp hh.2⟩
  obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp h.2
  have he : z = countingCenter38 n := hn
  exact ⟨n, (countingCenter_mem_central_iff38 N n).mp (he ▸ h.1), he⟩

theorem isolating_sorted_window_projection38 (L K : ℤ → ℂ) (p : ℂ → ℂ)
    (a b k : ℤ) (hk : a ≤ k ∧ k ≤ b) (s t : Multiset ℂ)
    (hL : ∀ i j : ℤ, i ≤ j → complexLexLE38 (L i) (L j))
    (hK : ∀ i j : ℤ, i ≤ j → complexLexLE38 (K i) (K j))
    (hLs : (Finset.Icc a b).val.map L = t) (hKs : (Finset.Icc a b).val.map K = s)
    (hmap : t.map p = s)
    (hmono : ∀ z ∈ t, ∀ w ∈ t, complexLexLE38 z w → complexLexLE38 (p z) (p w)) :
    p (L k) = K k := by
  have he : (integerWindow38 L a b).map p = integerWindow38 K a b := by
    rw [integerWindow_eq_sort38 L hL a b t hLs, integerWindow_eq_sort38 K hK a b s hKs]
    exact realType_sorted_projection38 s t p hmap hmono
  have hv := congrArg (fun l : List ℂ => l.getD (k - a).toNat (p 0)) he
  rw [List.getD_map, integerWindow_getD38 L hk] at hv
  have hi : (k - a).toNat < (integerWindow38 K a b).length := by
    simp only [integerWindow38, List.length_map, List.length_range]
    omega
  have hd : (integerWindow38 K a b).getD (k - a).toNat (p 0) =
      (integerWindow38 K a b).getD (k - a).toNat 0 := by
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi]
  rwa [hd, integerWindow_getD38 K hk] at hv

theorem isolating_periodic_projection_index38 {f : ℂ → ℂ} {N : ℕ}
    (hN : RootCountingAt38 f 2 N) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ)
    (hg : IsolatingGeometry38 C R c N)
    (hsub : ∀ n : ℤ, |n| ≤ (N : ℤ) → ball (C n) (R n) ⊆ ball 0 (countingRadius38 N))
    (hc : ∀ n : ℤ, |n| ≤ (N : ℤ) → (Lib.zeroMultiset f (ball (C n) (R n))).card = 2)
    {k : ℤ} (hk : periodicCentralIndex38 N k) :
    isolatingProjection38 C R N (periodicCandidate38 f N k) = countingCenter38 (k / 2) := by
  have hcov := isolating_central_coverage38 hN C R c hg hsub hc
  have hmap := isolating_projection_map38 hN C R c hg hsub hc
    (Lib.zeroMultiset (perChar 0) (ball 0 (countingRadius38 N)))
    (fun n hn => (isolating_free_count38 N n hn).1)
    (fun z hz => isolating_free_support38 N z (Or.inl hz))
  exact isolating_sorted_window_projection38 (periodicCandidate38 f N) freePeriodicSeq38
    (isolatingProjection38 C R N) _ _ k hk _ _
    (fun i j hij => periodicCandidate_mono38 hN hij) (fun i j hij => freePeriodicSeq_mono38 hij)
    (periodicCandidate_central_multiset38 hN) (freePeriodicSeq_window_multiset38 N)
    hmap (isolating_projection_mono38 hN C R c hg hcov)

theorem isolating_critical_projection_index38 {f : ℂ → ℂ} {N : ℕ}
    (hN : RootCountingAt38 f 1 N) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ)
    (hg : IsolatingGeometry38 C R c N)
    (hsub : ∀ n : ℤ, |n| ≤ (N : ℤ) → ball (C n) (R n) ⊆ ball 0 (countingRadius38 N))
    (hc : ∀ n : ℤ, |n| ≤ (N : ℤ) → (Lib.zeroMultiset f (ball (C n) (R n))).card = 1)
    {k : ℤ} (hk : criticalCentralIndex38 N k) :
    isolatingProjection38 C R N (criticalCandidate38 f N k) = countingCenter38 k := by
  have hcov := isolating_central_coverage38 hN C R c hg hsub hc
  have hmap := isolating_projection_map38 hN C R c hg hsub hc
    (Lib.zeroMultiset (deriv (discrim 0)) (ball 0 (countingRadius38 N)))
    (fun n hn => (isolating_free_count38 N n hn).2)
    (fun z hz => isolating_free_support38 N z (Or.inr hz))
  exact isolating_sorted_window_projection38 (criticalCandidate38 f N) countingCenter38
    (isolatingProjection38 C R N) _ _ k hk _ _
    (fun i j hij => criticalCandidate_mono38 hN hij) (fun i j hij => countingCenter_lex_mono38 hij)
    (criticalCandidate_central_multiset38 hN) (freeCriticalSeq_window_multiset38 N)
    hmap (isolating_projection_mono38 hN C R c hg hcov)

end
end NlsGge.GK38

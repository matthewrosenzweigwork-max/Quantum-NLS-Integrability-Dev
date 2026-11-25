import NlsGge.GK38.PeriodicLabellingOccurrence

/-! # S2: candidates enumerate roots with exact analytic multiplicity -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem rootEnumeration_of_blocks38 {f : ℂ → ℂ} {q N : ℕ}
    (h : RootCountingAt38 f q N) (L : ℤ → ℂ) (hroots : ∀ k : ℤ, f (L k) = 0)
    (hblocks : ∀ z : ℂ, f z = 0 → ∃ (S : Finset ℤ) (c : ℂ) (r : ℝ),
      z ∈ ball c r ∧ (∀ k : ℤ, L k = z → k ∈ S) ∧
        S.val.map L = Lib.zeroMultiset f (ball c r)) : RootEnumeration38 f L := by
  classical
  have hocc : ∀ z : ℂ, {k : ℤ | L k = z}.Finite ∧
      Set.encard {k : ℤ | L k = z} = analyticOrderAt f z := by
    intro z
    by_cases hz : f z = 0
    · obtain ⟨S, c, r, hmem, hs, hmap⟩ := hblocks z hz
      obtain ⟨hfin, he⟩ := finite_occurrence_count38 L z S hs
      refine ⟨hfin, ?_⟩
      rw [hmap, Lib.count_zeroMultiset_ball (h.2.1.mono (subset_univ _)), ite_eq_left hmem] at he
      exact he.trans (Nat.cast_analyticOrderNatAt (counting_order_ne_top38 h z))
    · have he : {k : ℤ | L k = z} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro k hk
        apply hz
        have hk' : L k = z := hk
        simpa only [hk'] using hroots k
      rw [he]
      refine ⟨Set.finite_empty, ?_⟩
      rw [Set.encard_empty, (h.2.1 z (mem_univ z)).analyticOrderAt_eq_zero.mpr hz]
  refine ⟨hroots, ?_, hocc⟩
  intro z
  constructor
  · intro hz
    have hne : {k : ℤ | L k = z} ≠ ∅ := by
      intro he
      have ho := (hocc z).2
      rw [he, Set.encard_empty] at ho
      exact (h.2.1 z (mem_univ z)).analyticOrderAt_eq_zero.mp ho.symm hz
    exact Set.nonempty_iff_ne_empty.mpr hne
  · rintro ⟨k, hk⟩
    simpa only [hk] using hroots k

theorem periodicCandidate_enumeration38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 2 N) : RootEnumeration38 f (periodicCandidate38 f N) := by
  classical
  apply rootEnumeration_of_blocks38 h _ (periodicCandidate_root38 h)
  intro z hz
  obtain hzN | ⟨n, hn, hzn⟩ := h.2.2.2.2.2.2 z hz
  · exact ⟨Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ) + 1), 0, countingRadius38 N,
      hzN, periodicCandidate_central_support38 h hzN, periodicCandidate_central_multiset38 h⟩
  · refine ⟨{2 * n, 2 * n + 1}, countingCenter38 n, Real.pi / 4,
      hzn, periodicCandidate_far_support38 h hn hzn, ?_⟩
    have hne : 2 * n ≠ 2 * n + 1 := by omega
    have heS : ({2 * n, 2 * n + 1} : Finset ℤ).val =
        (2 * n ::ₘ (2 * n + 1) ::ₘ 0) := by simp [hne]
    rw [heS, Multiset.map_cons, Multiset.map_cons, Multiset.map_zero]
    exact periodicCandidate_small_multiset38 h hn

theorem criticalCandidate_enumeration38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 1 N) : RootEnumeration38 f (criticalCandidate38 f N) := by
  classical
  apply rootEnumeration_of_blocks38 h _ (criticalCandidate_root38 h)
  intro z hz
  obtain hzN | ⟨n, hn, hzn⟩ := h.2.2.2.2.2.2 z hz
  · exact ⟨Finset.Icc (-(N : ℤ)) (N : ℤ), 0, countingRadius38 N,
      hzN, criticalCandidate_central_support38 h hzN, criticalCandidate_central_multiset38 h⟩
  · refine ⟨{n}, countingCenter38 n, Real.pi / 4,
      hzn, criticalCandidate_far_support38 h hn hzn, ?_⟩
    simpa only [Finset.singleton_val, Multiset.map_singleton] using
      criticalCandidate_small_multiset38 h hn

end
end NlsGge.GK38

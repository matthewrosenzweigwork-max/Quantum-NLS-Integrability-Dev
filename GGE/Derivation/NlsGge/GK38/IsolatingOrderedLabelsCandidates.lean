import NlsGge.GK38.IsolatingProjectionLabels

/-! Exact disc membership and multiplicity for the already certified candidates. -/
set_option autoImplicit false
open Set Metric Classical
namespace NlsGge.GK38
noncomputable section

theorem isolating_periodic_candidate_mem38 {f : ℂ → ℂ} {N : ℕ}
    (hN : RootCountingAt38 f 2 N) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ)
    (hg : IsolatingGeometry38 C R c N)
    (hsub : ∀ n : ℤ, |n| ≤ (N : ℤ) → ball (C n) (R n) ⊆ ball 0 (countingRadius38 N))
    (hc : ∀ n : ℤ, |n| ≤ (N : ℤ) → (Lib.zeroMultiset f (ball (C n) (R n))).card = 2)
    (k : ℤ) : periodicCandidate38 f N k ∈ ball (C (k / 2)) (R (k / 2)) := by
  by_cases hk : periodicCentralIndex38 N k
  · have hm := (counting_mem_zeroMultiset38 hN 0 (countingRadius38 N) _).mpr
      ⟨periodicCandidate_central_mem38 hN hk, periodicCandidate_root38 hN k⟩
    obtain ⟨n, hn, hzn⟩ := isolating_central_coverage38 hN C R c hg hsub hc _ hm
    have he := isolating_periodic_projection_index38 hN C R c hg hsub hc hk
    rw [isolating_projection_eq38 C R c N hg hn hzn] at he
    have hi := countingCenter_injective38 he
    simpa only [← hi] using hzn
  · obtain ⟨hC, hR, _⟩ := hg.2.2.2.2 (k / 2) (periodic_far_quotient38 hk)
    rw [hC, hR]
    exact periodicCandidate_far_mem38 hN hk

theorem isolating_critical_candidate_mem38 {f : ℂ → ℂ} {N : ℕ}
    (hN : RootCountingAt38 f 1 N) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ)
    (hg : IsolatingGeometry38 C R c N)
    (hsub : ∀ n : ℤ, |n| ≤ (N : ℤ) → ball (C n) (R n) ⊆ ball 0 (countingRadius38 N))
    (hc : ∀ n : ℤ, |n| ≤ (N : ℤ) → (Lib.zeroMultiset f (ball (C n) (R n))).card = 1)
    (k : ℤ) : criticalCandidate38 f N k ∈ ball (C k) (R k) := by
  by_cases hk : criticalCentralIndex38 N k
  · have hm := (counting_mem_zeroMultiset38 hN 0 (countingRadius38 N) _).mpr
      ⟨criticalCandidate_central_mem38 hN hk, criticalCandidate_root38 hN k⟩
    obtain ⟨n, hn, hzn⟩ := isolating_central_coverage38 hN C R c hg hsub hc _ hm
    have he := isolating_critical_projection_index38 hN C R c hg hsub hc hk
    rw [isolating_projection_eq38 C R c N hg hn hzn] at he
    have hi := countingCenter_injective38 he
    simpa only [← hi] using hzn
  · obtain ⟨hC, hR, _⟩ := hg.2.2.2.2 k (critical_far_index38 hk)
    rw [hC, hR]
    exact criticalCandidate_far_mem38 hN hk

theorem isolating_periodic_candidate_multiset38 {f : ℂ → ℂ} {N : ℕ}
    (hN : RootCountingAt38 f 2 N) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ)
    (hg : IsolatingGeometry38 C R c N)
    (hsub : ∀ n : ℤ, |n| ≤ (N : ℤ) → ball (C n) (R n) ⊆ ball 0 (countingRadius38 N))
    (hc : ∀ n : ℤ, |n| ≤ (N : ℤ) → (Lib.zeroMultiset f (ball (C n) (R n))).card = 2)
    (n : ℤ) :
    (periodicCandidate38 f N (2 * n) ::ₘ periodicCandidate38 f N (2 * n + 1) ::ₘ 0) =
      Lib.zeroMultiset f (ball (C n) (R n)) := by
  have hm := isolating_periodic_candidate_mem38 hN C R c hg hsub hc
  have he := rootEnumeration_window_multiset38 hN (periodicCandidate_enumeration38 hN)
    {2 * n, 2 * n + 1} (C n) (R n) (fun k => ?_)
  · have hne : 2 * n ≠ 2 * n + 1 := by omega
    simpa [hne] using he
  constructor
  · intro hk
    have hi : k / 2 = n := by
      by_contra hne
      exact Set.disjoint_left.mp (isolating_geometry_disjoint38 C R c N hg hne) (hm k) hk
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    have hi : k / 2 = n := by omega
    simpa only [hi] using hm k

theorem isolating_critical_candidate_multiset38 {f : ℂ → ℂ} {N : ℕ}
    (hN : RootCountingAt38 f 1 N) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ)
    (hg : IsolatingGeometry38 C R c N)
    (hsub : ∀ n : ℤ, |n| ≤ (N : ℤ) → ball (C n) (R n) ⊆ ball 0 (countingRadius38 N))
    (hc : ∀ n : ℤ, |n| ≤ (N : ℤ) → (Lib.zeroMultiset f (ball (C n) (R n))).card = 1)
    (n : ℤ) :
    ({criticalCandidate38 f N n} : Multiset ℂ) = Lib.zeroMultiset f (ball (C n) (R n)) := by
  have hm := isolating_critical_candidate_mem38 hN C R c hg hsub hc
  have he := rootEnumeration_window_multiset38 hN (criticalCandidate_enumeration38 hN)
    {n} (C n) (R n) (fun k => ?_)
  · simpa only [Finset.singleton_val, Multiset.map_singleton] using he
  rw [Finset.mem_singleton]
  constructor
  · intro hk
    by_contra hne
    exact Set.disjoint_left.mp (isolating_geometry_disjoint38 C R c N hg hne) (hm k) hk
  · intro he
    simpa only [he] using hm k

end
end NlsGge.GK38

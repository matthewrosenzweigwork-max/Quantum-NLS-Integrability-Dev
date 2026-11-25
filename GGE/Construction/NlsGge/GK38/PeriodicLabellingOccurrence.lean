import NlsGge.GK38.PeriodicLabellingRegions
import NlsGge.GK38.PeriodicLabellingLocal
import NlsGge.GK38.PeriodicLabellingMultiplicity

/-! # S2: finite occurrence supports in one counting block -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem finite_occurrence_count38 (L : ℤ → ℂ) (z : ℂ) (S : Finset ℤ)
    (hs : ∀ k : ℤ, L k = z → k ∈ S) :
    {k : ℤ | L k = z}.Finite ∧
      Set.encard {k : ℤ | L k = z} = ((S.val.map L).count z : ℕ∞) := by
  classical
  have he : {k : ℤ | L k = z} = ↑(S.filter fun k => z = L k) := by
    ext k
    simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq]
    constructor
    · intro hk
      exact ⟨hs k hk, hk.symm⟩
    · exact fun hk => hk.2.symm
  rw [he]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.encard_coe_eq_coe_finsetCard, Multiset.count_map]
  rfl

theorem periodicCandidate_central_support38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 2 N) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (countingRadius38 N)) :
    ∀ k : ℤ, periodicCandidate38 f N k = z →
      k ∈ Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ) + 1) := by
  intro k hk
  by_cases hkc : periodicCentralIndex38 N k
  · exact Finset.mem_Icc.mpr hkc
  · have hm := periodicCandidate_far_mem38 h hkc
    rw [hk] at hm
    exact ((Set.disjoint_left.mp (counting_central_small_disjoint38
      (periodic_far_quotient38 hkc))) hz hm).elim

theorem criticalCandidate_central_support38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 1 N) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (countingRadius38 N)) :
    ∀ k : ℤ, criticalCandidate38 f N k = z → k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  intro k hk
  by_cases hkc : criticalCentralIndex38 N k
  · exact Finset.mem_Icc.mpr hkc
  · have hm := criticalCandidate_far_mem38 h hkc
    rw [hk] at hm
    exact ((Set.disjoint_left.mp (counting_central_small_disjoint38
      (critical_far_index38 hkc))) hz hm).elim

theorem periodicCandidate_far_support38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 2 N) {n : ℤ} (hn : (N : ℤ) < |n|) {z : ℂ}
    (hz : z ∈ ball (countingCenter38 n) (Real.pi / 4)) :
    ∀ k : ℤ, periodicCandidate38 f N k = z → k ∈ ({2 * n, 2 * n + 1} : Finset ℤ) := by
  intro k hk
  by_cases hkc : periodicCentralIndex38 N k
  · have hm := periodicCandidate_central_mem38 h hkc
    rw [hk] at hm
    exact ((Set.disjoint_left.mp (counting_central_small_disjoint38 hn)) hm hz).elim
  · have hm := periodicCandidate_far_mem38 h hkc
    rw [hk] at hm
    have hq : k / 2 = n := by
      by_contra hne
      exact (Set.disjoint_left.mp (counting_small_ball_disjoint38 hne)) hm hz
    have hlo : 0 ≤ k % 2 := Int.emod_nonneg k (by norm_num)
    have hhi : k % 2 < 2 := Int.emod_lt_of_pos k (by norm_num)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

theorem criticalCandidate_far_support38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 1 N) {n : ℤ} (hn : (N : ℤ) < |n|) {z : ℂ}
    (hz : z ∈ ball (countingCenter38 n) (Real.pi / 4)) :
    ∀ k : ℤ, criticalCandidate38 f N k = z → k ∈ ({n} : Finset ℤ) := by
  intro k hk
  by_cases hkc : criticalCentralIndex38 N k
  · have hm := criticalCandidate_central_mem38 h hkc
    rw [hk] at hm
    exact ((Set.disjoint_left.mp (counting_central_small_disjoint38 hn)) hm hz).elim
  · have hm := criticalCandidate_far_mem38 h hkc
    rw [hk] at hm
    rw [Finset.mem_singleton]
    by_contra hne
    exact (Set.disjoint_left.mp (counting_small_ball_disjoint38 hne)) hm hz

end
end NlsGge.GK38

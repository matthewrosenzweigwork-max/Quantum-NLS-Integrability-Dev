import NlsGge.GK38.IsolatingPersistenceCounts
import NlsGge.GK38.IsolatingOrderedLabels

/-! GK I.12: local persistence of the complete fixed circle family.
Canonical sorted labels, all zero occurrences, and boundaries are retained. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem periodic_pair_root_cover38 (φ : PotPair) (z : ℂ) (hz : perChar φ z = 0) :
    ∃ n : ℤ, lamMinus φ n = z ∨ lamPlus φ n = z := by
  obtain ⟨k, hk⟩ := ((lamSeq_enumeration38 φ).2.1 z).mp hz
  have hlo : 0 ≤ k % 2 := Int.emod_nonneg k (by norm_num)
  have hhi : k % 2 < 2 := Int.emod_lt_of_pos k (by norm_num)
  refine ⟨k / 2, ?_⟩
  by_cases he : k % 2 = 0
  · left
    have heq : 2 * (k / 2) = k := by omega
    change lamSeq φ (2 * (k / 2)) = z
    rw [heq]
    exact hk
  · right
    have heq : 2 * (k / 2) + 1 = k := by omega
    change lamSeq φ (2 * (k / 2) + 1) = z
    rw [heq]
    exact hk

theorem fixed_family_persistence38 (φ₀ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : IsolatingFamily38 φ₀ C R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, ∃ N : ℕ, IsolatingGeometry38 C R c N ∧
      ∀ φ ∈ ball φ₀ ρ, IsolatingSpectral38 φ C R := by
  classical
  obtain ⟨ρ, hρ, c, N, hgeom, hfit, hcounts⟩ := fixed_family_local_counts38 φ₀ C R hfamily
  refine ⟨ρ, hρ, c, N, hgeom, fun φ hφ => ?_⟩
  obtain ⟨hp, hd, hm, hn, hc⟩ := hcounts φ hφ
  have hlabels := ordered_circle_labels38 φ C R c N hgeom hp hd hm hn hfit
    (fun n => ⟨(hc n).1, (hc n).2.1, (hc n).2.2.1, (hc n).2.2.2.1⟩)
  have hA : ∀ n : ℤ, lamMinus φ n ∈ ball (C n) (R n) := by
    intro n
    apply ((counting_mem_zeroMultiset38 hp _ _ _).mp ?_).1
    rw [← (hlabels n).1]
    simp
  have hB : ∀ n : ℤ, lamPlus φ n ∈ ball (C n) (R n) := by
    intro n
    apply ((counting_mem_zeroMultiset38 hp _ _ _).mp ?_).1
    rw [← (hlabels n).1]
    simp
  have hμ : ∀ n : ℤ, muSeq φ n ∈ ball (C n) (R n) := by
    intro n
    apply ((counting_mem_zeroMultiset38 hm _ _ _).mp ?_).1
    rw [← (hlabels n).2.1]
    simp
  have hν : ∀ n : ℤ, nuSeq38 φ n ∈ ball (C n) (R n) := by
    intro n
    apply ((counting_mem_zeroMultiset38 hn _ _ _).mp ?_).1
    rw [← (hlabels n).2.2.1]
    simp
  have hcrit : ∀ n : ℤ, lamDot φ n ∈ ball (C n) (R n) := by
    intro n
    apply ((counting_mem_zeroMultiset38 hd _ _ _).mp ?_).1
    rw [← (hlabels n).2.2.2]
    simp
  refine ⟨fun n => ⟨(convex_ball (C n) (R n)).segment_subset (hA n) (hB n),
    hμ n, hν n, hcrit n, (hlabels n).1, (hlabels n).2.1,
    (hlabels n).2.2.1, (hlabels n).2.2.2, (hc n).1, (hc n).2.1,
    (hc n).2.2.1, (hc n).2.2.2.1, (hc n).2.2.2.2⟩, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨n, he | he⟩ := periodic_pair_root_cover38 φ z hz
    · exact ⟨n, he ▸ hA n⟩
    · exact ⟨n, he ▸ hB n⟩
  · intro z hz
    obtain ⟨n, he⟩ := ((muSeq_enumeration38 φ).2.1 z).mp hz
    exact ⟨n, he ▸ hμ n⟩
  · intro z hz
    obtain ⟨n, he⟩ := ((nuSeq38_enumeration φ).2.1 z).mp hz
    exact ⟨n, he ▸ hν n⟩
  · intro z hz
    obtain ⟨n, he⟩ := ((lamDot_enumeration38 φ).2.1 z).mp hz
    exact ⟨n, he ▸ hcrit n⟩

end
end NlsGge.GK38

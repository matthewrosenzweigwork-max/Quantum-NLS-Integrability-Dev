import NlsGge.GK38.PeriodicLabellingRoots

/-! # S2: exact even/odd occurrence bookkeeping, including repeated roots -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

def RootEnumeration38 (f : ℂ → ℂ) (L : ℤ → ℂ) : Prop :=
  (∀ k : ℤ, f (L k) = 0) ∧
  (∀ z : ℂ, f z = 0 ↔ ∃ k : ℤ, L k = z) ∧
  (∀ z : ℂ, {k : ℤ | L k = z}.Finite ∧
    Set.encard {k : ℤ | L k = z} = analyticOrderAt f z)

theorem even_index_injective38 : Function.Injective (fun n : ℤ => 2 * n) := by
  intro n m h
  change 2 * n = 2 * m at h
  omega

theorem odd_index_injective38 : Function.Injective (fun n : ℤ => 2 * n + 1) := by
  intro n m h
  change 2 * n + 1 = 2 * m + 1 at h
  omega

theorem even_odd_occurrences_union38 (L : ℤ → ℂ) (z : ℂ) :
    (fun n : ℤ => 2 * n) '' {n : ℤ | L (2 * n) = z} ∪
      (fun n : ℤ => 2 * n + 1) '' {n : ℤ | L (2 * n + 1) = z} =
        {k : ℤ | L k = z} := by
  ext k
  constructor
  · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩) <;> exact hn
  · intro hk
    have hlo : 0 ≤ k % 2 := Int.emod_nonneg k (by norm_num)
    have hhi : k % 2 < 2 := Int.emod_lt_of_pos k (by norm_num)
    by_cases he : k % 2 = 0
    · left
      have heq : 2 * (k / 2) = k := by omega
      exact ⟨k / 2, by change L (2 * (k / 2)) = z; rw [heq]; exact hk, heq⟩
    · right
      have heq : 2 * (k / 2) + 1 = k := by omega
      exact ⟨k / 2, by change L (2 * (k / 2) + 1) = z; rw [heq]; exact hk, heq⟩

theorem even_odd_occurrences_disjoint38 (L : ℤ → ℂ) (z : ℂ) :
    Disjoint ((fun n : ℤ => 2 * n) '' {n : ℤ | L (2 * n) = z})
      ((fun n : ℤ => 2 * n + 1) '' {n : ℤ | L (2 * n + 1) = z}) := by
  rw [Set.disjoint_left]
  rintro k ⟨n, _, hn⟩ ⟨m, _, hm⟩
  change 2 * n = k at hn
  change 2 * m + 1 = k at hm
  omega

/-- The sum of the two subsequence occurrence counts is the whole analytic order. -/
theorem rootEnumeration_even_odd_encard38 {f : ℂ → ℂ} {L : ℤ → ℂ}
    (h : RootEnumeration38 f L) (z : ℂ) :
    Set.encard {n : ℤ | L (2 * n) = z} +
      Set.encard {n : ℤ | L (2 * n + 1) = z} = analyticOrderAt f z := by
  calc
    _ = Set.encard ((fun n : ℤ => 2 * n) '' {n : ℤ | L (2 * n) = z}) +
        Set.encard ((fun n : ℤ => 2 * n + 1) '' {n : ℤ | L (2 * n + 1) = z}) := by
      rw [even_index_injective38.encard_image, odd_index_injective38.encard_image]
    _ = _ := by
      rw [← Set.encard_union_eq (even_odd_occurrences_disjoint38 L z),
        even_odd_occurrences_union38]
      exact (h.2.2 z).2

theorem rootEnumeration_even_odd_bounds38 {f : ℂ → ℂ} {L : ℤ → ℂ}
    (h : RootEnumeration38 f L) (z : ℂ) :
    Set.encard {n : ℤ | L (2 * n) = z} ≤ analyticOrderAt f z ∧
      Set.encard {n : ℤ | L (2 * n + 1) = z} ≤ analyticOrderAt f z := by
  have he := rootEnumeration_even_odd_encard38 h z
  constructor
  · rw [← he]
    exact le_self_add
  · rw [← he]
    exact le_add_self

end
end NlsGge.GK38

import NlsGge.GK38.RealTypeSpectrum

/-! # S6: endpoint orders from actual combined occurrences

GK I.7. Both labels are counted at a collapsed gap.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem gap_indices_separated38 (u : PhysicalL2) {m n : ℤ} (hmn : m < n) :
    actualGapUpperAllE02_38 u m < actualGapLowerAllE02_38 u n := by
  have hl : StrictMono (actualGapLowerAllE02_38 u) := strictMono_int_of_lt_succ fun k =>
    (gap_endpoint_levels38 u k).1.trans_lt (gap_interlace u k)
  exact (gap_interlace u m).trans_le (hl.monotone (by omega))

theorem gap_interval_index_unique38 (u : PhysicalL2) {m n : ℤ} {x : ℝ}
    (hm : x ∈ Icc (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m))
    (hn : x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)) : m = n := by
  rcases lt_trichotomy m n with h | h | h
  · have := gap_indices_separated38 u h; linarith [hm.2, hn.1]
  · exact h
  · have := gap_indices_separated38 u h; linarith [hn.2, hm.1]

theorem gap_endpoint_eq_index38 (u : PhysicalL2) {m n : ℤ} {x y : ℝ}
    (hx : x ∈ Icc (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m))
    (hy : y ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n))
    (hxy : (x : ℂ) = (y : ℂ)) : m = n := by
  have he : x = y := Complex.ofReal_injective hxy
  exact gap_interval_index_unique38 u hx (he ▸ hy)

theorem gapLower_occurrences38 (u : PhysicalL2) (n : ℤ) :
    {m : ℤ | lamMinus (realSlice u) m = (actualGapLowerAllE02_38 u n : ℂ)} = {n} ∧
    {m : ℤ | lamPlus (realSlice u) m = (actualGapLowerAllE02_38 u n : ℂ)} =
      if actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n then {n} else ∅ := by
  classical
  have hlo := fun k => (gap_endpoint_levels38 u k).1
  constructor
  · ext m
    simp only [mem_ofPred_eq, mem_singleton_iff]
    rw [(lamPlus_real u m).2]
    constructor
    · exact gap_endpoint_eq_index38 u ⟨le_rfl, hlo m⟩ ⟨le_rfl, hlo n⟩
    · rintro rfl; rfl
  · ext m
    simp only [mem_ofPred_eq]
    rw [(lamPlus_real u m).1]
    by_cases hc : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n
    · simp only [hc, ite_eq_left, mem_singleton_iff]
      constructor
      · exact gap_endpoint_eq_index38 u ⟨hlo m, le_rfl⟩ ⟨hlo n, le_rfl⟩
      · rintro rfl; rfl
    · simp only [hc, ite_false, mem_empty_iff_false, iff_false]
      intro he
      have hm := gap_endpoint_eq_index38 u ⟨hlo m, le_rfl⟩ ⟨le_rfl, hlo n⟩ he
      subst m
      exact hc (Complex.ofReal_injective he).symm

theorem gapUpper_occurrences38 (u : PhysicalL2) (n : ℤ) :
    {m : ℤ | lamPlus (realSlice u) m = (actualGapUpperAllE02_38 u n : ℂ)} = {n} ∧
    {m : ℤ | lamMinus (realSlice u) m = (actualGapUpperAllE02_38 u n : ℂ)} =
      if actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n then {n} else ∅ := by
  classical
  have hlo := fun k => (gap_endpoint_levels38 u k).1
  constructor
  · ext m
    simp only [mem_ofPred_eq, mem_singleton_iff]
    rw [(lamPlus_real u m).1]
    constructor
    · exact gap_endpoint_eq_index38 u ⟨hlo m, le_rfl⟩ ⟨hlo n, le_rfl⟩
    · rintro rfl; rfl
  · ext m
    simp only [mem_ofPred_eq]
    rw [(lamPlus_real u m).2]
    by_cases hc : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n
    · simp only [← hc, ite_eq_left, mem_singleton_iff]
      constructor
      · exact gap_endpoint_eq_index38 u ⟨le_rfl, hlo m⟩ ⟨le_rfl, hlo n⟩
      · rintro rfl; rfl
    · simp only [hc, ite_false, mem_empty_iff_false, iff_false]
      intro he
      have hm := gap_endpoint_eq_index38 u ⟨le_rfl, hlo m⟩ ⟨hlo n, le_rfl⟩ he
      subst m
      exact hc (Complex.ofReal_injective he)

theorem order_at_gapEnd (u : PhysicalL2) (n : ℤ) :
    analyticOrderAt (perChar (realSlice u)) (actualGapLowerAllE02_38 u n : ℂ) =
      if actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n then (1 : ℕ∞) else 2 := by
  rw [← lamMinusPlus_occurrence38, (gapLower_occurrences38 u n).1,
    (gapLower_occurrences38 u n).2]
  by_cases hc : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n
  · norm_num [hc]
  · have ho := lt_of_le_of_ne (gap_endpoint_levels38 u n).1 hc
    simp [hc, ho]

theorem order_at_gapUpper38 (u : PhysicalL2) (n : ℤ) :
    analyticOrderAt (perChar (realSlice u)) (actualGapUpperAllE02_38 u n : ℂ) =
      if actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n then (1 : ℕ∞) else 2 := by
  rw [← lamMinusPlus_occurrence38, (gapUpper_occurrences38 u n).1,
    (gapUpper_occurrences38 u n).2]
  by_cases hc : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n
  · norm_num [hc]
  · have ho := lt_of_le_of_ne (gap_endpoint_levels38 u n).1 hc
    simp [hc, ho]

end
end NlsGge.GK38

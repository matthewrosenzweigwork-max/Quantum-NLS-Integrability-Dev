import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB5Shift

/-! # Track B, package 2: forward uniqueness for the approved solution class

Two `IsL2NLSSolution`s (owner-approved predicate) with the same datum at `0` agree for all `t ≥ 0`
(`forward_unique`). Proof: `τ = inf {t ≥ 0 | u t ≠ u' t}`; agreement on `[0,τ]` (continuity);
restart at `τ` with the shifted representatives (`PdeB5Shift`) and `duhamel_unique_short`.
Backward uniqueness (`t ≤ 0`) needs time reversal and is not treated here.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

theorem memLp_slab_one_of_isL4Loc {V : ℝ × PhysicalCircle → ℂ} (hV : IsL4Loc V) :
    MemLp V 4 (slabMeasure 1) :=
  (hV 1).mono_measure (by
    rw [slabMeasure_eq]
    exact Measure.restrict_mono (Set.prod_mono (Set.Icc_subset_Icc (by norm_num) le_rfl) le_rfl)
      le_rfl)

/-- **Forward uniqueness** in the approved class `IsL2NLSSolution`. -/
theorem forward_unique {u u' : ℝ → PhysicalL2} (hu : IsL2NLSSolution u)
    (hu' : IsL2NLSSolution u') (h0 : u 0 = u' 0) : ∀ t, 0 ≤ t → u t = u' t := by
  obtain ⟨hc, U, hrep, h4, -, hD⟩ := hu
  obtain ⟨hc', U', hrep', h4', -, hD'⟩ := hu'
  have step : ∀ τ, u τ = u' τ → ∃ ε > 0, ∀ t ∈ Set.Icc 0 ε, u (t + τ) = u' (t + τ) := by
    intro τ hτ
    obtain ⟨ε, hε, -, h⟩ := duhamel_unique_short one_pos le_rfl
      (memLp_slab_one_of_isL4Loc (isL4Loc_shift h4 τ))
      (memLp_slab_one_of_isL4Loc (isL4Loc_shift h4' τ))
      (ae_restrict_of_ae (isSpacetimeRep_shift hrep τ).slice)
      (ae_restrict_of_ae (isSpacetimeRep_shift hrep' τ).slice)
      (by simpa using hτ) (fun t _ => ((isHm1Duhamel_shift h4 hD τ) t).2)
      (fun t _ => ((isHm1Duhamel_shift h4' hD' τ) t).2)
    exact ⟨ε, hε, h⟩
  by_contra hne
  push Not at hne
  set D : Set ℝ := {t : ℝ | 0 ≤ t ∧ u t ≠ u' t} with hDdef
  have hDne : D.Nonempty := by
    obtain ⟨t, ht, h⟩ := hne
    exact ⟨t, ht, h⟩
  have hDbdd : BddBelow D := ⟨0, fun t ht => ht.1⟩
  set τ := sInf D with hτdef
  have hτ0 : 0 ≤ τ := le_csInf hDne fun t ht => ht.1
  have hbelow : ∀ t, 0 ≤ t → t < τ → u t = u' t := fun t ht htτ => by
    by_contra h
    exact absurd (csInf_le hDbdd ⟨ht, h⟩) (not_le.2 htτ)
  have hclosed : IsClosed {t | u t = u' t} := isClosed_eq hc hc'
  have hτeq : u τ = u' τ := by
    rcases hτ0.eq_or_lt with h | h
    · rw [← h]; exact h0
    · have hmem : τ ∈ closure (Set.Ico 0 τ) := by
        rw [closure_Ico h.ne]; exact ⟨hτ0, le_rfl⟩
      exact (hclosed.closure_subset_iff.2 (fun t ht => hbelow t ht.1 ht.2)) hmem
  obtain ⟨ε, hε, hstep⟩ := step τ hτeq
  have hlb : τ + ε ≤ τ := by
    refine le_csInf hDne fun t ht => ?_
    by_contra hlt
    push Not at hlt
    have htτ : τ ≤ t := csInf_le hDbdd ht
    have h := hstep (t - τ) ⟨by linarith, by linarith⟩
    rw [sub_add_cancel] at h
    exact ht.2 h
  linarith

end

end LiebLiniger.FixedPeriod.ALLS.PdeB

import NlsGge.GK38.ProductRepr
import NlsGge.Spectral.ActualGapActionAllNE02_38

/-! # S5: actual endpoint levels, root reality and strict separation

GK book I.7. Existing endpoints are the realized quasimomentum level intervals.
No label continuity, multiplicity formula or regularity restriction is assumed.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem perChar_root_real38 (u : PhysicalL2) (z : ℂ)
    (hz : perChar (realSlice u) z = 0) : z.im = 0 := by
  rw [perChar_realSlice] at hz
  have hrad : actualPhysicalUnitHalfTrace32 u z ^ 2 - 1 = 0 :=
    (mul_eq_zero.mp hz).resolve_left (by norm_num)
  exact actualPhysicalUnitBranchRadicand_eq_zero_im32 u z hrad

theorem gap_endpoint_levels38 (u : PhysicalL2) (n : ℤ) :
    actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n ∧
    actualQuasimomentumRealPartE02_38 u (actualGapLowerAllE02_38 u n) = (n : ℝ) * Real.pi ∧
    actualQuasimomentumRealPartE02_38 u (actualGapUpperAllE02_38 u n) = (n : ℝ) * Real.pi := by
  obtain ⟨⟨x, hx⟩, hI⟩ := actualGapLevelSet_eq_Icc_E02_38 u n
  rw [hI] at hx
  have hab := hx.1.trans hx.2
  have hl : actualGapLowerAllE02_38 u n ∈ actualGapLevelSetE02_38 u n := by
    rw [hI]; exact ⟨le_rfl, hab⟩
  have hu : actualGapUpperAllE02_38 u n ∈ actualGapLevelSetE02_38 u n := by
    rw [hI]; exact ⟨hab, le_rfl⟩
  exact ⟨hab, hl, hu⟩

theorem gap_endpoint_roots38 (u : PhysicalL2) (n : ℤ) :
    perChar (realSlice u) (actualGapLowerAllE02_38 u n : ℂ) = 0 ∧
    perChar (realSlice u) (actualGapUpperAllE02_38 u n : ℂ) = 0 := by
  obtain ⟨hl, hu⟩ := actualGapEndpoint_halfTrace_all_E02_38 u n
  have hc : (Real.cos ((n : ℝ) * Real.pi) : ℂ) ^ 2 = 1 := by
    exact_mod_cast real_cos_int_mul_pi_sq_E02_38 n
  constructor
  · rw [perChar_realSlice, hl, hc]; ring
  · rw [perChar_realSlice, hu, hc]; ring

/-- Integer levels have no ambiguity because pi is nonzero. -/
theorem gap_level_index_unique38 {n m : ℤ}
    (h : (n : ℝ) * Real.pi = (m : ℝ) * Real.pi) : n = m := by
  exact_mod_cast mul_right_cancel₀ Real.pi_ne_zero h

theorem gap_interlace (u : PhysicalL2) (n : ℤ) :
    actualGapUpperAllE02_38 u n < actualGapLowerAllE02_38 u (n + 1) := by
  by_contra h
  have hm := (monotone_actualQuasimomentumRealPartE02_38 u) (le_of_not_gt h)
  rw [(gap_endpoint_levels38 u (n + 1)).2.1, (gap_endpoint_levels38 u n).2.2] at hm
  push_cast at hm
  linarith [Real.pi_pos]

/-- A characteristic root lies at one unique integer quasimomentum level. -/
theorem perChar_real_root_level38 (u : PhysicalL2) (x : ℝ)
    (hx : perChar (realSlice u) (x : ℂ) = 0) :
    ∃! n : ℤ, actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi := by
  have ht : actualPhysicalUnitHalfTrace32 u (x : ℂ) = 1 ∨
      actualPhysicalUnitHalfTrace32 u (x : ℂ) = -1 := by
    have hh : (actualPhysicalUnitHalfTrace32 u (x : ℂ) - 1) *
        (actualPhysicalUnitHalfTrace32 u (x : ℂ) + 1) = 0 := by
      rw [perChar_realSlice] at hx
      linear_combination (1 / 4 : ℂ) * hx
    simpa only [sub_eq_zero, add_eq_zero_iff_eq_neg] using mul_eq_zero.mp hh
  have hex : ∃ n : ℤ, actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi := by
    have hc := actualQuasimomentumBoundaryE02_38_cos u x
    rcases ht with ht | ht
    · rw [ht] at hc
      obtain ⟨k, hk⟩ := Complex.cos_eq_one_iff.mp hc
      refine ⟨2 * k, ?_⟩
      have hr := congrArg Complex.re hk
      norm_num [Complex.mul_re] at hr
      change (actualQuasimomentumBoundaryE02_38 u x).re = _
      push_cast
      nlinarith
    · rw [ht] at hc
      obtain ⟨k, hk⟩ := Complex.cos_eq_neg_one_iff.mp hc
      refine ⟨2 * k + 1, ?_⟩
      have hr := congrArg Complex.re hk
      norm_num [Complex.mul_re] at hr
      change (actualQuasimomentumBoundaryE02_38 u x).re = _
      push_cast
      linarith
  obtain ⟨n, hn⟩ := hex
  exact ⟨n, hn, fun m hm => gap_level_index_unique38 (hm.symm.trans hn)⟩

theorem perChar_root_eq_level_endpoint38 (u : PhysicalL2) (x : ℝ) (n : ℤ)
    (hx : perChar (realSlice u) (x : ℂ) = 0)
    (hp : actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi) :
    x = actualGapLowerAllE02_38 u n ∨ x = actualGapUpperAllE02_38 u n := by
  have hI : x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
    rw [← (actualGapLevelSet_eq_Icc_E02_38 u n).2]
    exact hp
  have hv : actualGapHeightE02_38 u x = 0 := by
    apply (actualGapHeightE02_38_eq_zero_iff u x).mpr
    rw [perChar_realSlice] at hx
    have hh : actualPhysicalUnitHalfTrace32 u (x : ℂ) ^ 2 = 1 := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (by norm_num))
    have hn := congrArg norm hh
    rw [norm_pow, norm_one] at hn
    nlinarith [norm_nonneg (actualPhysicalUnitHalfTrace32 u (x : ℂ))]
  by_contra h
  push Not at h
  have ha : actualGapLowerAllE02_38 u n < x := lt_of_le_of_ne hI.1 h.1.symm
  have hb : x < actualGapUpperAllE02_38 u n := lt_of_le_of_ne hI.2 h.2
  have hs := actualGapHeight_ge_semicircle_all_E02_38 u n x hI
  have hpos : 0 < gapSemicircle (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) x :=
    Real.sqrt_pos.mpr (mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb))
  rw [hv] at hs
  linarith

theorem perChar_zero_iff (u : PhysicalL2) (z : ℂ) :
    perChar (realSlice u) z = 0 ↔ ∃ n : ℤ,
      z = (actualGapLowerAllE02_38 u n : ℂ) ∨ z = (actualGapUpperAllE02_38 u n : ℂ) := by
  constructor
  · intro hz
    have hr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [perChar_root_real38 u z hz])
    obtain ⟨n, hn, _⟩ := perChar_real_root_level38 u z.re (by rwa [← hr])
    rcases perChar_root_eq_level_endpoint38 u z.re n (by rwa [← hr]) hn with he | he
    · exact ⟨n, Or.inl (hr.trans (congrArg Complex.ofReal he))⟩
    · exact ⟨n, Or.inr (hr.trans (congrArg Complex.ofReal he))⟩
  · rintro ⟨n, hz | hz⟩
    · rw [hz]; exact (gap_endpoint_roots38 u n).1
    · rw [hz]; exact (gap_endpoint_roots38 u n).2

end
end NlsGge.GK38

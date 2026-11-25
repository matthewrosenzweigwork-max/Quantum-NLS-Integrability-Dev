import NlsGge.GK38.ActionEllipseDomain
import NlsGge.Spectral.ActualGapHeightHolderE02_38

set_option autoImplicit false
open Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
namespace NlsGge.GK38.ActionGapLocalization
noncomputable section

theorem real_gap_mem_segment (u : PhysicalL2) (n : ℤ) {x : ℝ}
    (hx : x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)) :
    (x : ℂ) ∈ segment ℝ (lamMinus (realSlice u) n) (lamPlus (realSlice u) n) := by
  rw [(lamPlus_real u n).2, (lamPlus_real u n).1]
  obtain ⟨a, b, ha, hb, hab, he⟩ :=
    (Icc_subset_segment hx : x ∈ segment ℝ (actualGapLowerAllE02_38 u n)
      (actualGapUpperAllE02_38 u n))
  refine ⟨a, b, ha, hb, hab, ?_⟩
  simpa only [smul_eq_mul, Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul]
    using congrArg (fun y : ℝ => (y : ℂ)) he

theorem height_zero_off_cuts (u : PhysicalL2) (x : ℝ)
    (hx : (x : ℂ) ∉ gapSegments38 (realSlice u)) : actualGapHeightE02_38 u x = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := actualGapHeight_mem_gap_of_ne_zero_E02_38 u x h
  exact hx (mem_iUnion.mpr ⟨n, real_gap_mem_segment u n ⟨hn.1.le, hn.2.le⟩⟩)

theorem own_gap_inside_diameter (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 (realSlice u) C R) (n : ℤ) :
    (C n).re - R n < actualGapLowerAllE02_38 u n ∧
      actualGapUpperAllE02_38 u n < (C n).re + R n := by
  obtain ⟨κ, N, _, hs⟩ := hf
  have hlo := (hs.1 n).1 (left_mem_segment ℝ (lamMinus (realSlice u) n) (lamPlus (realSlice u) n))
  have hup := (hs.1 n).1 (right_mem_segment ℝ (lamMinus (realSlice u) n) (lamPlus (realSlice u) n))
  have hl : |(lamMinus (realSlice u) n).re - (C n).re| < R n :=
    (Complex.abs_re_le_norm (lamMinus (realSlice u) n - C n)).trans_lt (mem_ball_iff_norm.mp hlo)
  have hu : |(lamPlus (realSlice u) n).re - (C n).re| < R n :=
    (Complex.abs_re_le_norm (lamPlus (realSlice u) n - C n)).trans_lt (mem_ball_iff_norm.mp hup)
  rw [(lamPlus_real u n).2, Complex.ofReal_re] at hl
  rw [(lamPlus_real u n).1, Complex.ofReal_re] at hu
  exact ⟨by linarith [(abs_lt.mp hl).1], by linarith [(abs_lt.mp hu).2]⟩

theorem height_zero_on_diameter_outside_own (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 (realSlice u) C R) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc ((C n).re - R n) ((C n).re + R n))
    (ho : x ∉ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)) :
    actualGapHeightE02_38 u x = 0 := by
  by_contra h
  obtain ⟨m, hm⟩ := actualGapHeight_mem_gap_of_ne_zero_E02_38 u x h
  obtain ⟨κ, N, hg, hs⟩ := hf
  have hb := (hs.1 m).1 (real_gap_mem_segment u m ⟨hm.1.le, hm.2.le⟩)
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have ht := contour_left_bound38 C R κ N hg hmn hb
    simp only [Complex.ofReal_re] at ht
    linarith [hx.1]
  · subst m
    exact ho ⟨hm.1.le, hm.2.le⟩
  · have ht := contour_right_bound38 C R κ N hg hnm hb
    simp only [Complex.ofReal_re] at ht
    linarith [hx.2]


theorem height_integral_diameter_eq_gap (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 (realSlice u) C R) (n : ℤ) :
    (∫ x in ((C n).re - R n)..((C n).re + R n), actualGapHeightE02_38 u x) =
      ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        actualGapHeightE02_38 u x := by
  have hb := own_gap_inside_diameter u C R hf n
  have hord : actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
    obtain ⟨x, hx⟩ := (actualGapLevelSet_eq_Icc_E02_38 u n).1
    rw [(actualGapLevelSet_eq_Icc_E02_38 u n).2] at hx
    exact hx.1.trans hx.2
  have hi (a b : ℝ) : IntervalIntegrable (actualGapHeightE02_38 u) volume a b :=
    (continuous_actualGapHeightE02_38 u).intervalIntegrable a b
  have hl : (∫ x in ((C n).re - R n)..(actualGapLowerAllE02_38 u n),
      actualGapHeightE02_38 u x) = 0 := by
    calc
      _ = ∫ _x in ((C n).re - R n)..(actualGapLowerAllE02_38 u n), (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hb.1.le
        intro x hx
        apply height_zero_on_diameter_outside_own u C R hf n x
        · exact ⟨hx.1.le, (hx.2.le.trans hord).trans hb.2.le⟩
        · exact fun ho => (not_lt_of_ge ho.1) hx.2
      _ = 0 := by simp
  have hu : (∫ x in (actualGapUpperAllE02_38 u n)..((C n).re + R n),
      actualGapHeightE02_38 u x) = 0 := by
    calc
      _ = ∫ _x in (actualGapUpperAllE02_38 u n)..((C n).re + R n), (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hb.2.le
        intro x hx
        apply height_zero_on_diameter_outside_own u C R hf n x
        · exact ⟨hb.1.le.trans (hord.trans hx.1.le), hx.2.le⟩
        · exact fun ho => (not_lt_of_ge ho.2) hx.1
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hi ((C n).re - R n) (actualGapLowerAllE02_38 u n))
    (hi (actualGapLowerAllE02_38 u n) ((C n).re + R n))
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (hi (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n))
    (hi (actualGapUpperAllE02_38 u n) ((C n).re + R n))
  rw [hl, zero_add] at hsplit
  rw [hu, add_zero] at hright
  exact hsplit.symm.trans hright.symm

end
end NlsGge.GK38.ActionGapLocalization

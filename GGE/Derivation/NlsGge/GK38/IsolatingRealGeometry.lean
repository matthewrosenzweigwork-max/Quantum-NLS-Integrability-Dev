import NlsGge.GK38.IsolatingCirclePatch
import NlsGge.GK38.IsolatingCounting

/-! Actual real-slice gap circles. The common certified central window gives
strict margins at both interfaces with the exact standard tails. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem real_interval_subset_circle38 (a b : ℝ) (C : ℂ) (r : ℝ) (hC : C.im = 0)
    (ha : (a : ℂ) ∈ ball C r) (hb : (b : ℂ) ∈ ball C r) :
    Icc a b ⊆ {x : ℝ | (x : ℂ) ∈ ball C r} := by
  have ha' : |a - C.re| < r := by
    simpa only [mem_ball_iff_norm, realType_norm_sub_real38 _ _ (Complex.ofReal_im _) hC,
      Complex.ofReal_re] using ha
  have hb' : |b - C.re| < r := by
    simpa only [mem_ball_iff_norm, realType_norm_sub_real38 _ _ (Complex.ofReal_im _) hC,
      Complex.ofReal_re] using hb
  intro x hx
  change (x : ℂ) ∈ ball C r
  rw [mem_ball_iff_norm, realType_norm_sub_real38 _ _ (Complex.ofReal_im _) hC, Complex.ofReal_re]
  exact abs_lt.mpr ⟨by linarith [(abs_lt.mp ha').1, hx.1], by linarith [(abs_lt.mp hb').2, hx.2]⟩

theorem real_center_geometry38 (u : PhysicalL2) :
    ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ c : ℝ, ∃ N : ℕ, IsolatingGeometry38 C R c N ∧
      ∀ n : ℤ, Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) ⊆
        {x : ℝ | (x : ℂ) ∈ ball (C n) (R n)} := by
  obtain ⟨U, hU, N, _, hcount⟩ := prescribed_common_counting38 (realSlice u) 1
  have hp := (hcount (realSlice u) (mem_of_mem_nhds hU)).1
  have hcentral : ∀ n : ℤ, |n| ≤ (N : ℤ) →
      |actualGapLowerAllE02_38 u n| < countingRadius38 N ∧
      |actualGapUpperAllE02_38 u n| < countingRadius38 N := by
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := abs_le.mp hn
    have hl : lamMinus (realSlice u) n ∈ ball (0 : ℂ) (countingRadius38 N) := by
      change lamSeq (realSlice u) (2 * n) ∈ _
      rw [lamSeq_eq_candidate38 _ hp]
      exact periodicCandidate_central_mem38 hp (by dsimp only [periodicCentralIndex38]; omega)
    have hu : lamPlus (realSlice u) n ∈ ball (0 : ℂ) (countingRadius38 N) := by
      change lamSeq (realSlice u) (2 * n + 1) ∈ _
      rw [lamSeq_eq_candidate38 _ hp]
      exact periodicCandidate_central_mem38 hp (by dsimp only [periodicCentralIndex38]; omega)
    rw [(lamPlus_real u n).2] at hl
    rw [(lamPlus_real u n).1] at hu
    exact ⟨by simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using hl,
      by simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using hu⟩
  let lo : ℤ → ℝ := fun n => if |n| ≤ (N : ℤ) then actualGapLowerAllE02_38 u n
    else (n : ℝ) * Real.pi - Real.pi / 4
  let hi : ℤ → ℝ := fun n => if |n| ≤ (N : ℤ) then actualGapUpperAllE02_38 u n
    else (n : ℝ) * Real.pi + Real.pi / 4
  have hle : ∀ n : ℤ, lo n ≤ hi n := by
    intro n
    by_cases hn : |n| ≤ (N : ℤ)
    · simpa only [lo, hi, ite_eq_left hn] using (gap_endpoint_levels38 u n).1
    · simp only [lo, hi, ite_eq_right hn]
      linarith [Real.pi_pos]
  have hgap : ∀ n : ℤ, hi n < lo (n + 1) := by
    intro n
    by_cases hn : |n| ≤ (N : ℤ) <;> by_cases hn' : |n + 1| ≤ (N : ℤ)
    · simpa only [lo, hi, ite_eq_left hn, ite_eq_left hn'] using
        gap_indices_separated38 u (show n < n + 1 from by omega)
    · have hne : n = (N : ℤ) := by
        obtain ⟨hlo, hhi⟩ := abs_le.mp hn
        by_contra hh
        exact hn' (abs_le.mpr ⟨by omega, by omega⟩)
      have hbound := (abs_lt.mp (hcentral n hn).2).2
      have hnr : (n : ℝ) = (N : ℝ) := by exact_mod_cast hne
      simp only [lo, hi, ite_eq_left hn, ite_eq_right hn', Int.cast_add, Int.cast_one]
      unfold countingRadius38 at hbound
      rw [hnr]
      nlinarith [Real.pi_pos]
    · have hne : n + 1 = -(N : ℤ) := by
        obtain ⟨hlo, hhi⟩ := abs_le.mp hn'
        by_contra hh
        exact hn (abs_le.mpr ⟨by omega, by omega⟩)
      have hbound := (abs_lt.mp (hcentral (n + 1) hn').1).1
      have hnr : (n : ℝ) + 1 = -(N : ℝ) := by exact_mod_cast hne
      simp only [lo, hi, ite_eq_right hn, ite_eq_left hn']
      unfold countingRadius38 at hbound
      nlinarith [Real.pi_pos]
    · simp only [lo, hi, ite_eq_right hn, ite_eq_right hn', Int.cast_add, Int.cast_one]
      nlinarith [Real.pi_pos]
  have htail : ∀ n : ℤ, (N : ℤ) < |n| → lo n = (n : ℝ) * Real.pi - Real.pi / 4 ∧
      hi n = (n : ℝ) * Real.pi + Real.pi / 4 := by
    intro n hn
    simp only [lo, hi, ite_eq_right (not_le.mpr hn), and_self]
  obtain ⟨C, R, c, hgeom, hfinite⟩ := real_interval_circle_patch38 lo hi N hle hgap htail
  refine ⟨C, R, c, N, hgeom, fun n => ?_⟩
  by_cases hn : |n| ≤ (N : ℤ)
  · simpa only [lo, hi, ite_eq_left hn] using hfinite n hn
  · have hn' : (N : ℤ) < |n| := lt_of_not_ge hn
    have hpair : (lamMinus (realSlice u) n ::ₘ lamPlus (realSlice u) n ::ₘ 0) =
        Lib.zeroMultiset (perChar (realSlice u)) (ball (countingCenter38 n) (Real.pi / 4)) := by
      simpa only [lamMinus, lamPlus, lamSeq_eq_candidate38 _ hp] using periodicCandidate_small_multiset38 hp hn'
    have hl : lamMinus (realSlice u) n ∈ ball (countingCenter38 n) (Real.pi / 4) := by
      apply ((counting_mem_zeroMultiset38 hp _ _ _).mp ?_).1
      rw [← hpair]
      simp
    have hu : lamPlus (realSlice u) n ∈ ball (countingCenter38 n) (Real.pi / 4) := by
      apply ((counting_mem_zeroMultiset38 hp _ _ _).mp ?_).1
      rw [← hpair]
      simp
    rw [(lamPlus_real u n).2] at hl
    rw [(lamPlus_real u n).1] at hu
    obtain ⟨hc, hr, _⟩ := hgeom.2.2.2.2 n hn'
    rw [hc, hr]
    exact real_interval_subset_circle38 _ _ _ _ (by simp [countingCenter38]) hl hu

end
end NlsGge.GK38

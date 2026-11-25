import NlsGge.GK38.PeriodicLabelling

/-! # S3: one local cutoff bounds all three actual label sequences

This uses the accepted canonical cutoff compatibility, including the central
block. It asserts no continuity of individual complex labels. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

/-- The finite central spectral block has a uniform displacement bound. -/
theorem counting_central_shift_bound38 (N : ℕ) (n : ℤ) (z : ℂ)
    (hn : |n| ≤ (N : ℤ)) (hz : z ∈ ball (0 : ℂ) (countingRadius38 N)) :
    ‖z - countingCenter38 n‖ ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4 := by
  have hc := countingCenter_low_norm38 hn
  have hzn : ‖z‖ < (N : ℝ) * Real.pi + Real.pi / 4 := by
    simpa only [mem_ball, dist_zero_right, countingRadius38] using hz
  have h := norm_sub_le z (countingCenter38 n)
  linarith

/-- Every certified periodic candidate has bounded shift, with exact far-disc localization. -/
theorem periodicCandidate_shift_bound38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 2 N) (k : ℤ) :
    ‖periodicCandidate38 f N k - countingCenter38 (k / 2)‖ ≤
        2 * (N : ℝ) * Real.pi + Real.pi / 4 ∧
      ((N : ℤ) < |k / 2| →
        ‖periodicCandidate38 f N k - countingCenter38 (k / 2)‖ < Real.pi / 4) := by
  have hb : Real.pi / 4 ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4 := by
    have hh : 0 ≤ 2 * (N : ℝ) * Real.pi := by positivity
    linarith
  by_cases hk : periodicCentralIndex38 N k
  · have hn : |k / 2| ≤ (N : ℤ) := by
      unfold periodicCentralIndex38 at hk
      apply abs_le.mpr
      omega
    refine ⟨counting_central_shift_bound38 N _ _ hn (periodicCandidate_central_mem38 h hk), ?_⟩
    intro hfar
    omega
  · have hm := mem_ball_iff_norm.mp (periodicCandidate_far_mem38 h hk)
    exact ⟨hm.le.trans hb, fun _ => hm⟩

/-- The critical candidates obey the same all-index and far-index bounds. -/
theorem criticalCandidate_shift_bound38 {f : ℂ → ℂ} {N : ℕ}
    (h : RootCountingAt38 f 1 N) (n : ℤ) :
    ‖criticalCandidate38 f N n - countingCenter38 n‖ ≤
        2 * (N : ℝ) * Real.pi + Real.pi / 4 ∧
      ((N : ℤ) < |n| →
        ‖criticalCandidate38 f N n - countingCenter38 n‖ < Real.pi / 4) := by
  have hb : Real.pi / 4 ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4 := by
    have hh : 0 ≤ 2 * (N : ℝ) * Real.pi := by positivity
    linarith
  by_cases hn : criticalCentralIndex38 N n
  · have hlow : |n| ≤ (N : ℤ) := abs_le.mpr hn
    refine ⟨counting_central_shift_bound38 N _ _ hlow (criticalCandidate_central_mem38 h hn), ?_⟩
    intro hfar
    omega
  · have hm := mem_ball_iff_norm.mp (criticalCandidate_far_mem38 h hn)
    exact ⟨hm.le.trans hb, fun _ => hm⟩

/-- One neighbourhood and cutoff give a full-sequence shift bound and all far quarter discs. -/
theorem labelling_local_bounds38 (φ₀ : PotPair) :
  ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, 0 < N ∧
    ∀ φ : PotPair, φ ∈ U →
      (∀ n : ℤ,
        ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4 ∧
        ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4 ∧
        ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4) ∧
      (∀ n : ℤ, (N : ℤ) < |n| →
        ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 ∧
        ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4 ∧
        ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4) := by
  obtain ⟨U, hU, N, hN⟩ := simultaneous_counting_lemma38 φ₀
  refine ⟨U, hU, N, (hN φ₀ (mem_of_mem_nhds hU)).1.1, fun φ hφ => ?_⟩
  obtain ⟨hp, hd⟩ := hN φ hφ
  have hm (n : ℤ) := periodicCandidate_shift_bound38 hp (2 * n)
  have hp' (n : ℤ) := periodicCandidate_shift_bound38 hp (2 * n + 1)
  have hd' (n : ℤ) := criticalCandidate_shift_bound38 hd n
  have heP := lamSeq_eq_candidate38 φ hp
  have heD := lamDot_eq_candidate38 φ hd
  have hminus (n : ℤ) :
      ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4 ∧
      ((N : ℤ) < |n| → ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4) := by
    simpa only [lamMinus, heP, (periodic_index_pair38 n).1, countingCenter38] using hm n
  have hplus (n : ℤ) :
      ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4 ∧
      ((N : ℤ) < |n| → ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4) := by
    simpa only [lamPlus, heP, (periodic_index_pair38 n).2.1, countingCenter38] using hp' n
  have hdot (n : ℤ) :
      ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 2 * (N : ℝ) * Real.pi + Real.pi / 4 ∧
      ((N : ℤ) < |n| → ‖lamDot φ n - (n : ℂ) * (Real.pi : ℂ)‖ < Real.pi / 4) := by
    simpa only [heD, countingCenter38] using hd' n
  exact ⟨fun n => ⟨(hminus n).1, (hplus n).1, (hdot n).1⟩,
    fun n hn => ⟨(hminus n).2 hn, (hplus n).2 hn, (hdot n).2 hn⟩⟩

end
end NlsGge.GK38

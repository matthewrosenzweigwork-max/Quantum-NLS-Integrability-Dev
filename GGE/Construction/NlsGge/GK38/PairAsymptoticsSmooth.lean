import NlsGge.GK38.PairAsymptoticsOscillatory

/-! # F5: smooth approximation in the interval L1 norm (GK Appendix D.1) -/

set_option autoImplicit false

open Filter Topology MeasureTheory Set
open scoped ContDiff

namespace NlsGge.GK38

noncomputable section

theorem exists_smooth_l1_approx38 (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧
      (∫ s : ℝ in 0..1, ‖f s - g s‖) ≤ ε := by
  obtain ⟨g, hgs, hfg, hgc, hgi⟩ :=
    hf.1.exists_hasCompactSupport_integral_sub_le (half_pos hε)
  obtain ⟨u, hu, hgu⟩ :=
    (hgs.uniformContinuous_of_continuous hgc).exists_contDiff_dist_le (half_pos hε)
  have hfgI : IntervalIntegrable (fun s => ‖f s - g s‖) volume 0 1 :=
    (hf.sub (hgc.intervalIntegrable _ _)).norm
  have hguI : IntervalIntegrable (fun s => ‖g s - u s‖) volume 0 1 :=
    ((hgc.intervalIntegrable _ _).sub (hu.continuous.intervalIntegrable _ _)).norm
  have hfuI : IntervalIntegrable (fun s => ‖f s - u s‖) volume 0 1 :=
    (hf.sub (hu.continuous.intervalIntegrable _ _)).norm
  refine ⟨u, hu, ?_⟩
  calc (∫ s : ℝ in 0..1, ‖f s - u s‖)
      ≤ ∫ s : ℝ in 0..1, ‖f s - g s‖ + ‖g s - u s‖ := by
        refine intervalIntegral.integral_mono_on zero_le_one hfuI (hfgI.add hguI)
          (fun s _ => ?_)
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = (∫ s : ℝ in 0..1, ‖f s - g s‖) + ∫ s : ℝ in 0..1, ‖g s - u s‖ :=
        intervalIntegral.integral_add hfgI hguI
    _ ≤ ε / 2 + ε / 2 := by
      apply add_le_add
      · simpa only [intervalIntegral.integral_of_le zero_le_one] using hfg
      · calc (∫ s : ℝ in 0..1, ‖g s - u s‖) ≤ ∫ _s : ℝ in 0..1, ε / 2 := by
               apply intervalIntegral.integral_mono_on zero_le_one hguI intervalIntegrable_const
               intro s _
               simpa only [dist_eq_norm, norm_sub_rev] using (hgu s).le
             _ = ε / 2 := by simp
    _ = ε := add_halves ε

end

end NlsGge.GK38

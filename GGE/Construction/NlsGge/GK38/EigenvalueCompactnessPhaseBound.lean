import NlsGge.GK38.EigenvalueCompactnessPhaseRealization

/-! # S7/D2: phase displacement from the actual L1 coefficient bound

This bound does not assert uniformly small spectral tails.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem periodicPhase_displacement38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : ‖a‖ = 1) (t : Time38) :
    |periodicPhase38 u x a t - x * (t : ℝ)| ≤ ‖u‖ := by
  have hi := periodicPhase_intervalIntegrable38 u x a ha t
  have hU : IntervalIntegrable (fun r => ‖e02Pot38 u r‖) volume 0 1 := intervalIntegrable_norm_coverRep38_one u
  have hUt := hU.mono_set (uIcc_subset_uIcc (left_mem_uIcc : (0 : ℝ) ∈ uIcc (0 : ℝ) 1)
    (by simpa only [uIcc_of_le zero_le_one] using t.2))
  have hb : ∀ r ∈ Icc (0 : ℝ) t, |(e02Pot38 u r *
      (periodicState38 u x a r 1 / periodicState38 u x a r 0)).re| ≤ ‖e02Pot38 u r‖ := by
    intro r hr
    have hn := periodicState_ratio_norm38 u x a (unit_direction_ne_zero38 a ha) r
      ⟨hr.1, hr.2.trans (t.2.2.trans (by norm_num))⟩
    exact (Complex.abs_re_le_norm _).trans_eq (by rw [norm_mul, hn, mul_one])
  have hh : (∫ r in (0 : ℝ)..(t : ℝ), |(e02Pot38 u r *
      (periodicState38 u x a r 1 / periodicState38 u x a r 0)).re|) ≤
      ∫ r in (0 : ℝ)..(t : ℝ), ‖e02Pot38 u r‖ :=
    intervalIntegral.integral_mono_on t.2.1 hi.abs hUt hb
  have hm : (∫ r in (0 : ℝ)..(t : ℝ), ‖e02Pot38 u r‖) ≤ ∫ r in (0 : ℝ)..1, ‖e02Pot38 u r‖ :=
    intervalIntegral.integral_mono_interval le_rfl t.2.1 t.2.2
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hU
  have he : periodicPhase38 u x a t - x * (t : ℝ) =
      -(∫ r in (0 : ℝ)..(t : ℝ), (e02Pot38 u r *
        (periodicState38 u x a r 1 / periodicState38 u x a r 0)).re) := by
    unfold periodicPhase38 periodicState38
    ring
  rw [he, abs_neg]
  exact (intervalIntegral.abs_integral_le_integral_abs t.2.1).trans
    (hh.trans (hm.trans (integral_coverRep38_le_one u)))

end
end NlsGge.GK38

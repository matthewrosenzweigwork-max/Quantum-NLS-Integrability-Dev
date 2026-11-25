import QuantumNLS.LOCAL017HaarOperators
import QuantumNLS.ResetMoserCone
import QuantumNLS.Ext025A4BanachSeries
import QuantumNLS.GP05AcceptedBridgeR16

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.LOCAL017SourceR19
open Ext025A4BanachComplexification Ext025A4BanachSeries
open D01LocalPrimitive
abbrev H := D01LocalPrimitive.K
abbrev Form := ResetMoser.Form
abbrev CH := LOCAL017Haar.CH
abbrev CF := Cx Form

/-- A common complex form extension, with its quadratic vanishing order. -/
theorem source_form (S : ResetMoser.Hyp) :
    ∃ R > (0 : ℝ), R ≤ S.R ∧ ∃ C ≥ (0 : ℝ), ∃ g : CH → CF,
      AnalyticOnNhd ℂ g (ball 0 R) ∧
      (∀ z ∈ ball (0 : CH) R, ‖g z‖ ≤ C * ‖z‖^2) ∧
      (∀ x ∈ ball (0 : H) R, g (Cx.ι x) = Cx.ι (ResetMoser.Dl S x)) := by
  have ha : AnalyticAt ℝ (ResetMoser.Dl S) 0 :=
    (RealAnalyticDef.analyticAt_of_isRealAnalyticPoly
      (S.Ω_analytic 0 (mem_ball_self S.R_pos))).sub analyticAt_const
  obtain ⟨p, r, hp⟩ := ha
  obtain ⟨r', hr'0, hr'r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  obtain ⟨C, _, hC⟩ := p.norm_mul_pow_le_of_lt_radius (hr'r.trans_le hp.r_le)
  have hr : 0 < (r' : ℝ) := by exact_mod_cast hr'0
  have hp' : HasFPowerSeriesOnBall (ResetMoser.Dl S) p 0 (ENNReal.ofReal r') := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hp.mono hr'0 hr'r.le
  have hd0 : ResetMoser.Dl S 0 = 0 := by
    obtain ⟨B, hB⟩ := S.Ω_quad
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa [ResetMoser.Dl] using hB 0 (mem_ball_self S.R_pos)) (norm_nonneg _)
  have hdf : fderiv ℝ (ResetMoser.Dl S) 0 = 0 := by
    rw [(ResetMoser.Dl_hasFDerivAt S (mem_ball_self S.R_pos)).fderiv, S.fderiv_Ω_zero]
  have hp0 : p 0 = 0 := by
    apply ContinuousMultilinearMap.ext
    intro v
    simpa [hd0] using hp.coeff_zero v
  have hp1 : p 1 = 0 := by
    have hh := hp.hasFPowerSeriesAt.fderiv_eq
    rw [hdf] at hh
    exact (continuousMultilinearCurryFin1 ℝ H Form).injective (by simpa using hh.symm)
  let q := cxSeries p
  let g : CH → CF := fun z => q.sum (z - Cx.ι (0 : H))
  have hg := series_sum_hasSeries p (0 : H) hr hC
  have hi0 : Cx.ι (0 : H) = (0 : CH) := by apply Cx.ext <;> rfl
  rw [hi0] at hg
  have hq0 : q 0 = 0 := by simp [q, cxSeries, hp0]
  have hq1 : q 1 = 0 := by simp [q, cxSeries, hp1]
  have hsmall := hg.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 2
  have he : ∀ z : CH, q.partialSum 2 z = 0 := by
    intro z
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, hq0, hq1]
  obtain ⟨B, hB⟩ := hsmall.bound
  have hb : ∀ᶠ z : CH in 𝓝 0, ‖g z‖ ≤ max B 0 * ‖z‖^2 := by
    filter_upwards [hB] with z hz
    simp only [zero_add, sub_zero] at hz
    change ‖q.sum z - q.partialSum 2 z‖ ≤ B * ‖‖z‖^2‖ at hz
    rw [he, sub_zero, norm_pow, norm_norm] at hz
    simpa only [g, hi0, sub_zero] using
      hz.trans (mul_le_mul_of_nonneg_right (le_max_left B 0) (by positivity))
  obtain ⟨d, hd, hdb⟩ := Metric.mem_nhds_iff.mp hb
  let R := min S.R (min (r'/2) d)
  have hR : 0 < R := lt_min S.R_pos (lt_min (by positivity) hd)
  have hRr : R ≤ r'/2 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨R, hR, min_le_left _ _, max B 0, le_max_right _ _, g, ?_, ?_, ?_⟩
  · exact hg.analyticOnNhd.mono (by simpa only [Metric.eball_ofReal] using ball_subset_ball hRr)
  · intro z hz
    exact hdb ((ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))) hz)
  · intro x hx
    exact series_sum_real hp' x ((ball_subset_ball (by linarith : R ≤ (r' : ℝ))) hx)

end QuantumNLS.LOCAL017SourceR19

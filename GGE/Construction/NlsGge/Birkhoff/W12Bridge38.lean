import NlsGge.Birkhoff.W12Tilt38g
import NlsGge.Birkhoff.S04Moments38e
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.SpectralFoundations NlsGge.Sobolev38
open scoped ENNReal ContDiff

/-! W12 bridge (review REVIEW_W12 finding F1): the spectral `EB38` agrees with v2's charge series
`∑ β_{j+1} Q_{2j}` on every field of `𝓕⁻¹E_s` and on `μ_W`-a.e. field. -/

namespace NlsGge.Birkhoff

/-- Every field of `𝓕⁻¹E_s`: `E_B` equals the charge series of a smooth representative. -/
theorem EB38_eq_chargeSeries_FinvE38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (u : FinvE38 c s) :
    ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u.1 ∧ EB38 c.val u.1 = chargeSeriesW38 (bCoef38 c.val) U := by
  obtain ⟨U, hU, hper, hUu⟩ := exists_smooth_rep38 (physOfE38 c s (toE38 c s u))
    (fun m => sobolev_physOfE38 c s (m : ℝ) (toE38 c s u))
  rw [physOfE38_toE38] at hUu
  refine ⟨U, hU, hper, hUu, ?_⟩
  rw [← hUu]; exact EB38_eq_chargeSeries c U hU hper

/-- `μ_W`-a.e. field: `E_B` equals the charge series of a smooth representative. -/
theorem BirkhoffInput38.ae_EB38_eq_chargeSeries {lower upper : ℝ} (B : BirkhoffInput38) (c : BoundedCoefficients lower upper) :
    ∀ᵐ u ∂(B.muW38 c.val), ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u ∧ EB38 c.val u = chargeSeriesW38 (bCoef38 c.val) U := by
  filter_upwards [B.ae_muW38_smooth lower upper c.val (coef_lower38 c) (coef_bound38 c)
    (coef_upper38 c)] with u ⟨U, hU, hper, hUu⟩
  refine ⟨U, hU, hper, hUu, ?_⟩
  rw [← hUu]; exact EB38_eq_chargeSeries c U hU hper

end NlsGge.Birkhoff

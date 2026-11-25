import NlsGge.GK38.ActionGradientQuotient

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.Pilot
namespace NlsGge.GK38.ActionGradient
noncomputable section

def directionQuotient (φ h : PotPair) (z : ℂ) : ℂ :=
  gradDiscrimCLM φ z h / canonRoot38 φ z

theorem directionQuotient_analytic (φ : PotPair) (hφ : φ ∈ gkW) (h : PotPair) :
    AnalyticOnNhd ℂ (directionQuotient φ h) (actionCutDomain38 φ) := by
  let ev : (PotPair →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ h
  have ha : AnalyticOnNhd ℂ (fun z => ev (gradRootQuotient φ z)) (actionCutDomain38 φ) := by
    intro z hz
    exact (ev.analyticAt _).comp (gradRootQuotient_fibre_analytic φ hφ z hz)
  have he : (fun z => ev (gradRootQuotient φ z)) = directionQuotient φ h := by
    funext z
    change (canonRoot38 φ z)⁻¹ * gradDiscrimCLM φ z h = _
    rw [directionQuotient, div_eq_mul_inv, mul_comm]
  rwa [he] at ha

theorem gradient_circle_integration_by_parts (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) (h : PotPair) :
    CircleIntegrable (directionQuotient φ h) (C n) (R n) ∧
    CircleIntegrable (fun z => z * deriv (directionQuotient φ h) z) (C n) (R n) ∧
    circleIntegral (fun z => z * deriv (directionQuotient φ h) z) (C n) (R n) =
      -circleIntegral (directionQuotient φ h) (C n) (R n) := by
  have hs := fixed_sphere_subset φ C R hf n
  have hr := isolating_radius_pos38 hf n
  have hq := directionQuotient_analytic φ hφ h
  have hi : CircleIntegrable (directionQuotient φ h) (C n) (R n) :=
    (hq.continuousOn.mono hs).circleIntegrable hr.le
  have hzi : CircleIntegrable (fun z => z * deriv (directionQuotient φ h) z) (C n) (R n) :=
    ((analyticOnNhd_id.mul hq.deriv).continuousOn.mono hs).circleIntegrable hr.le
  have hsum := hi.add hzi
  have hp : ∀ z ∈ sphere (C n) (R n),
      HasDerivWithinAt (fun w => w * directionQuotient φ h w)
        (directionQuotient φ h z + z * deriv (directionQuotient φ h) z)
        (sphere (C n) (R n)) z := by
    intro z hz
    have hd : HasDerivAt (fun w : ℂ => w * directionQuotient φ h w)
        (directionQuotient φ h z + z * deriv (directionQuotient φ h) z) z := by
      convert (hasDerivAt_id z).mul (hq z (hs hz)).differentiableAt.hasDerivAt using 1 <;>
        (first | rfl | simp only [id_eq, one_mul])
    exact hd.hasDerivWithinAt
  have hz := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr.le hp
  rw [circleIntegral.integral_add hi hzi] at hz
  exact ⟨hi, hzi, eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using hz)⟩

end
end NlsGge.GK38.ActionGradient

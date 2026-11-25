import NlsGge.GK38.GradTauGammaMomentVariation

/-! The two periodic moment integrations by parts. Circle integrability is
established before each splitting or closed-contour derivative identity. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem k4aDirectionQuotient_analytic38 (φ h : PotPair) :
    AnalyticOnNhd ℂ (k4aDirectionQuotient38 φ h) {z : ℂ | perChar φ z ≠ 0} := by
  let ev : (PotPair →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ h
  have hD : AnalyticOnNhd ℂ (fun z => gradDiscrimCLM φ z h) univ := by
    intro z _
    exact (ev.analyticAt _).comp
      ((ActionGradient.gradDiscrim_joint_analytic (φ, z) (mem_univ _)).comp
        ((analyticAt_const (v := φ)).prod analyticAt_id))
  intro z hz
  exact ((analyticOnNhd_discrim_z φ z (mem_univ _)).mul
    (hD z (mem_univ _))).div (analyticOnNhd_perChar_z φ z (mem_univ _)) hz

theorem k4aDirectionCircleIntegrable38 (φ h : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (k4aDirectionQuotient38 φ h) (C n) (R n) := by
  exact ((k4aDirectionQuotient_analytic38 φ h).continuousOn.mono
    (fun z hz => isolating_periodic_boundary38 hf n z hz)).circleIntegrable
      (isolating_radius_pos38 hf n).le

theorem k4aDirectionCircleIBP1_38 (φ h : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (fun z => z * deriv (k4aDirectionQuotient38 φ h) z) (C n) (R n) ∧
      circleIntegral (fun z => z * deriv (k4aDirectionQuotient38 φ h) z) (C n) (R n) =
        -circleIntegral (k4aDirectionQuotient38 φ h) (C n) (R n) := by
  have hr := isolating_radius_pos38 hf n
  have hs := isolating_periodic_boundary38 hf n
  have hQ := k4aDirectionQuotient_analytic38 φ h
  have hi := k4aDirectionCircleIntegrable38 φ h C R hf n
  have hzi : CircleIntegrable (fun z => z * deriv (k4aDirectionQuotient38 φ h) z)
      (C n) (R n) :=
    ((analyticOnNhd_id.mul hQ.deriv).continuousOn.mono
      (fun z hz => hs z hz)).circleIntegrable hr.le
  have hp : ∀ z ∈ sphere (C n) (R n),
      HasDerivWithinAt (fun w => w * k4aDirectionQuotient38 φ h w)
        (k4aDirectionQuotient38 φ h z + z * deriv (k4aDirectionQuotient38 φ h) z)
        (sphere (C n) (R n)) z := by
    intro z hz
    have hd := (hasDerivAt_id z).mul (hQ z (hs z hz)).differentiableAt.hasDerivAt
    simp only [id_eq, one_mul] at hd
    exact hd.hasDerivWithinAt
  have hz := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr.le hp
  rw [circleIntegral.integral_add hi hzi] at hz
  exact ⟨hzi, eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using hz)⟩

theorem k4aDirectionCircleIBP2_38 (φ h : PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (fun z => z ^ 2 * deriv (k4aDirectionQuotient38 φ h) z) (C n) (R n) ∧
      circleIntegral (fun z => z ^ 2 * deriv (k4aDirectionQuotient38 φ h) z) (C n) (R n) =
        -2 * circleIntegral (fun z => z * k4aDirectionQuotient38 φ h z) (C n) (R n) := by
  have hr := isolating_radius_pos38 hf n
  have hs := isolating_periodic_boundary38 hf n
  have hQ := k4aDirectionQuotient_analytic38 φ h
  have hi : CircleIntegrable (fun z => 2 * (z * k4aDirectionQuotient38 φ h z))
      (C n) (R n) :=
    ((analyticOnNhd_const.mul (analyticOnNhd_id.mul hQ)).continuousOn.mono
      (fun z hz => hs z hz)).circleIntegrable hr.le
  have hzi : CircleIntegrable (fun z => z ^ 2 * deriv (k4aDirectionQuotient38 φ h) z)
      (C n) (R n) :=
    (((analyticOnNhd_id.pow 2).mul hQ.deriv).continuousOn.mono
      (fun z hz => hs z hz)).circleIntegrable hr.le
  have hp : ∀ z ∈ sphere (C n) (R n),
      HasDerivWithinAt (fun w => w ^ 2 * k4aDirectionQuotient38 φ h w)
        (2 * (z * k4aDirectionQuotient38 φ h z) +
          z ^ 2 * deriv (k4aDirectionQuotient38 φ h) z)
        (sphere (C n) (R n)) z := by
    intro z hz
    have hd := ((hasDerivAt_id z).pow 2).mul
      (hQ z (hs z hz)).differentiableAt.hasDerivAt
    convert hd.hasDerivWithinAt using 1 <;> (first | rfl | simp; ring)
  have hz := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr.le hp
  rw [circleIntegral.integral_add hi hzi, circleIntegral.integral_const_mul] at hz
  refine ⟨hzi, ?_⟩
  linear_combination hz

end
end NlsGge.GK38

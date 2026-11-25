import NlsGge.GK38.ActionBranchDerivative
import NlsGge.Analysis.ArcIntegrationByParts
import NlsGge.GK38.ActionEllipseContinuity

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.Analysis.EllipseDeformation NlsGge.GK38.ActionEllipseContinuity
namespace NlsGge.GK38.ActionUpperArc
noncomputable section

theorem quotient_analytic (u : PhysicalL2) :
    AnalyticOnNhd ℂ (fun z => deriv (discrim (realSlice u)) z /
      canonRoot38 (realSlice u) z) (actionCutDomain38 (realSlice u)) := by
  intro z hz
  have hp : (realSlice u, z) ∈ rootDomain38 := ⟨realSlice_mem_gkW u, hz⟩
  have hnum := (NlsGge.GK38.analyticOnNhd_discrimDeriv_joint38
    (realSlice u, z) (mem_univ _)).comp
    ((analyticAt_const (v := realSlice u)).prod analyticAt_id)
  have hden := (canonRoot_analytic38 (realSlice u, z) hp).comp
    ((analyticAt_const (v := realSlice u)).prod analyticAt_id)
  exact hnum.div hden (canonRoot_ne_zero38 (realSlice u) hp.1 z hp.2)

theorem upperPrimitive_hasDeriv (u : PhysicalL2) (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (upperPrimitive u)
      (deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z) z := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  have he : upperPrimitive u =ᶠ[𝓝 z]
      (fun w => -Complex.I * actualQuasimomentumE02_38 u w) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
    unfold upperPrimitive
    rw [extendFrom_extends hk.1.continuousOn w hw]
  exact (NlsGge.GK38.ActionBranch.primitive_hasDeriv_upper u z hz).congr_of_eventuallyEq he

theorem curve_upper_closed (c r δ θ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    0 ≤ (curve (c : ℂ) r δ θ).im := by
  rw [NlsGge.GK38.ActionEllipseDomain.curve_im (c : ℂ) r δ θ (by simp)]
  exact mul_nonneg (mul_nonneg hδ.le hr.le) (Real.sin_nonneg_of_mem_Icc hθ)

theorem curve_upper_open (c r δ θ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    0 < (curve (c : ℂ) r δ θ).im := by
  rw [NlsGge.GK38.ActionEllipseDomain.curve_im (c : ℂ) r δ θ (by simp)]
  exact mul_pos (mul_pos hδ hr) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

theorem actual_upper_arc_integration_by_parts (u : PhysicalL2) (c r δ : ℝ)
    (hr : 0 < r) (hδ : 0 < δ)
    (hs : sphere (c : ℂ) r ⊆ actionCutDomain38 (realSlice u)) :
    IntervalIntegrable (fun θ => velocity r δ θ *
      actionIntegrand38 (realSlice u) (curve (c : ℂ) r δ θ)) volume 0 Real.pi ∧
    IntervalIntegrable (fun θ => velocity r δ θ *
      upperPrimitive u (curve (c : ℂ) r δ θ)) volume 0 Real.pi ∧
    (∫ θ in (0 : ℝ)..Real.pi, velocity r δ θ *
      actionIntegrand38 (realSlice u) (curve (c : ℂ) r δ θ)) =
      curve (c : ℂ) r δ Real.pi * upperPrimitive u (curve (c : ℂ) r δ Real.pi) -
      curve (c : ℂ) r δ 0 * upperPrimitive u (curve (c : ℂ) r δ 0) -
      ∫ θ in (0 : ℝ)..Real.pi, velocity r δ θ *
        upperPrimitive u (curve (c : ℂ) r δ θ) := by
  have hcurve : Continuous (curve (c : ℂ) r δ) :=
    continuous_iff_continuousAt.mpr (fun θ => (curve_derivative (c : ℂ) r δ θ).continuousAt)
  have hF : ContinuousOn (fun θ => upperPrimitive u (curve (c : ℂ) r δ θ))
      (uIcc (0 : ℝ) Real.pi) := by
    rw [uIcc_of_le Real.pi_pos.le]
    exact (upperPrimitive_continuous u).comp hcurve.continuousOn
      (fun θ hθ => curve_upper_closed c r δ θ hr hδ hθ)
  have hf : ContinuousOn (fun θ => deriv (discrim (realSlice u)) (curve (c : ℂ) r δ θ) /
      canonRoot38 (realSlice u) (curve (c : ℂ) r δ θ)) (uIcc (0 : ℝ) Real.pi) := by
    apply (quotient_analytic u).continuousOn.comp hcurve.continuousOn
    intro θ _
    exact NlsGge.GK38.ActionEllipseDomain.ellipse_avoids_cut u (c : ℂ) r δ (by simp) hr hδ hs θ
  have hd : ∀ θ ∈ Ioo (min (0 : ℝ) Real.pi) (max (0 : ℝ) Real.pi),
      HasDerivAt (upperPrimitive u)
        (deriv (discrim (realSlice u)) (curve (c : ℂ) r δ θ) /
          canonRoot38 (realSlice u) (curve (c : ℂ) r δ θ))
        (curve (c : ℂ) r δ θ) := by
    intro θ hθ
    rw [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at hθ
    exact upperPrimitive_hasDeriv u _ (curve_upper_open c r δ θ hr hδ hθ)
  have h := NlsGge.Analysis.ArcIntegrationByParts.arc_integration_by_parts
    (F := upperPrimitive u)
    (f := fun z : ℂ => deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z)
    (curve_derivative (c : ℂ) r δ) (velocity_continuous r δ) hF hf hd
  simpa only [actionIntegrand38, mul_div_assoc] using h

end
end NlsGge.GK38.ActionUpperArc

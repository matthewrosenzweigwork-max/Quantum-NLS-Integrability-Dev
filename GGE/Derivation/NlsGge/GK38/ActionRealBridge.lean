import NlsGge.GK38.ActionCircleReduction
import NlsGge.GK38.ActionEllipseCosine
import NlsGge.GK38.ActionGapLocalization

set_option autoImplicit false
open Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
namespace NlsGge.GK38.ActionRealBridge
noncomputable section

theorem circle_integral_eq_height (u : PhysicalL2) (c r : ℝ) (hr : 0 < r)
    (hs : sphere (c : ℂ) r ⊆ actionCutDomain38 (realSlice u)) :
    circleIntegral (actionIntegrand38 (realSlice u)) (c : ℂ) r =
      2 * (((∫ x in (c - r)..(c + r), actualGapHeightE02_38 u x) : ℝ) : ℂ) := by
  let P : ℝ → ℂ := fun δ => ∫ θ in (0 : ℝ)..Real.pi,
    NlsGge.Analysis.EllipseDeformation.velocity r δ θ *
      NlsGge.GK38.ActionEllipseContinuity.upperPrimitive u (NlsGge.Analysis.EllipseDeformation.curve (c : ℂ) r δ θ)
  have hp : ContinuousOn P (Icc (0 : ℝ) 1) :=
    (NlsGge.GK38.ActionEllipseContinuity.upper_integral_continuity u (c : ℂ) r (by simp) hr.le).2
  have hG : ContinuousOn (fun δ => (-2 : ℂ) * ((P δ).re : ℂ)) (Icc (0 : ℝ) 1) :=
    continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (Complex.continuous_re.comp_continuousOn hp))
  have hz := NlsGge.Analysis.CompactParametricIntegral.closed_endpoint_of_positive_constant hG
    (K := circleIntegral (actionIntegrand38 (realSlice u)) (c : ℂ) r)
    (fun δ hδ => (NlsGge.GK38.ActionCircleReduction.circle_integral_eq_neg_two_upper_primitive_re
      u c r δ hr hδ.1 hs).symm)
  have hflat : (P 0).re = -(∫ x in (c - r)..(c + r), actualGapHeightE02_38 u x) :=
    NlsGge.GK38.ActionEllipseCosine.flattened_upper_integral_re u c r
  rw [hflat, Complex.ofReal_neg] at hz
  simpa only [neg_mul_neg] using hz.symm

theorem contour_action_family_real (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 (realSlice u) C R) (n : ℤ) :
    contourAction38 (realSlice u) (C n) (R n) = (actualGapActionAllE02_38 u n : ℂ) := by
  have hcopy := hf
  obtain ⟨κ, N, hg, _⟩ := hcopy
  have hr := (hg.1 n).1
  have hcenter : C n = ((C n).re : ℂ) :=
    Complex.ext (by simp) (by simp [(hg.1 n).2])
  have hs : sphere (C n) (R n) ⊆ actionCutDomain38 (realSlice u) := by
    simpa only [sub_zero, one_smul, zero_smul, add_zero, one_mul, zero_mul] using
      action_contour_sphere_subset38 (realSlice u) C C R R hf hf n 0 ⟨le_rfl, zero_le_one⟩
  have hc := circle_integral_eq_height u (C n).re (R n) hr (by rwa [← hcenter])
  rw [← hcenter, NlsGge.GK38.ActionGapLocalization.height_integral_diameter_eq_gap u C R hf n] at hc
  unfold contourAction38
  rw [hc]
  simp only [actualGapActionAllE02_38, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

theorem action_real_bridge (u : PhysicalL2) (n : ℤ) :
    gkActionC38 (realSlice u) n = (actualGapActionAllE02_38 u n : ℂ) :=
  contour_action_family_real u (discC (realSlice u)) (discR (realSlice u))
    (isolating_family38 (realSlice u) (realSlice_mem_gkW u)) n

end
end NlsGge.GK38.ActionRealBridge

import NlsGge.GK38.ActionEllipseDomain
import NlsGge.Analysis.CompactParametricIntegral
import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38

set_option autoImplicit false
open Set Metric MeasureTheory Filter Topology
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.ActionEllipseContinuity
noncomputable section

def upperPrimitive (u : PhysicalL2) (z : ℂ) : ℂ :=
  -Complex.I * extendFrom {w : ℂ | 0 < w.im} (actualQuasimomentumE02_38 u) z

theorem upperPrimitive_continuous (u : PhysicalL2) :
    ContinuousOn (upperPrimitive u) {z : ℂ | 0 ≤ z.im} :=
  continuousOn_const.mul (continuousOn_extend_actualQuasimomentumE02_38 u)

theorem curve_joint_continuous (c : ℂ) (r : ℝ) :
    Continuous (fun p : ℝ × ℝ => NlsGge.Analysis.EllipseDeformation.curve c r p.1 p.2) := by
  unfold NlsGge.Analysis.EllipseDeformation.curve
  fun_prop

theorem velocity_joint_continuous (r : ℝ) :
    Continuous (fun p : ℝ × ℝ => NlsGge.Analysis.EllipseDeformation.velocity r p.1 p.2) := by
  unfold NlsGge.Analysis.EllipseDeformation.velocity
  fun_prop

theorem upper_rectangle (c : ℂ) (r : ℝ) (hc : c.im = 0) (hr : 0 ≤ r)
    {δ θ : ℝ} (hδ : δ ∈ Icc (0 : ℝ) 1) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    0 ≤ (NlsGge.Analysis.EllipseDeformation.curve c r δ θ).im := by
  rw [NlsGge.GK38.ActionEllipseDomain.curve_im c r δ θ hc]
  exact mul_nonneg (mul_nonneg hδ.1 hr) (Real.sin_nonneg_of_mem_Icc hθ)

theorem upper_integral_continuity (u : PhysicalL2) (c : ℂ) (r : ℝ)
    (hc : c.im = 0) (hr : 0 ≤ r) :
    (∀ δ ∈ Icc (0 : ℝ) 1, IntervalIntegrable
      (fun θ => NlsGge.Analysis.EllipseDeformation.velocity r δ θ *
        upperPrimitive u (NlsGge.Analysis.EllipseDeformation.curve c r δ θ)) volume 0 Real.pi) ∧
      ContinuousOn (fun δ => ∫ θ in (0 : ℝ)..Real.pi,
        NlsGge.Analysis.EllipseDeformation.velocity r δ θ *
          upperPrimitive u (NlsGge.Analysis.EllipseDeformation.curve c r δ θ)) (Icc (0 : ℝ) 1) := by
  apply NlsGge.Analysis.CompactParametricIntegral.continuousOn_rectangle_integral zero_le_one Real.pi_pos.le
  apply (velocity_joint_continuous r).continuousOn.mul
  exact (upperPrimitive_continuous u).comp (curve_joint_continuous c r).continuousOn
    (fun p hp => upper_rectangle c r hc hr hp.1 hp.2)

end
end NlsGge.GK38.ActionEllipseContinuity

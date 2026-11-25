import NlsGge.Analysis.ArcIntegrationByParts
import NlsGge.GK38.ActionEllipseContinuity
import NlsGge.Spectral.ActualGapHeightSemicircleE02_38

set_option autoImplicit false
open Set MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.ActionEllipseCosine
noncomputable section

theorem cosine_substitution (g : ℝ → ℂ) (hg : Continuous g) (c r : ℝ) :
    IntervalIntegrable (fun θ => NlsGge.Analysis.EllipseDeformation.velocity r 0 θ *
      g (c + r * Real.cos θ)) volume 0 Real.pi ∧
      IntervalIntegrable g volume (c + r) (c - r) ∧
      (∫ θ in (0 : ℝ)..Real.pi, NlsGge.Analysis.EllipseDeformation.velocity r 0 θ *
        g (c + r * Real.cos θ)) = ∫ x in (c + r)..(c - r), g x := by
  have hd (θ : ℝ) : HasDerivAt (fun θ => c + r * Real.cos θ)
      (-r * Real.sin θ) θ := by
    convert (hasDerivAt_const θ c).add ((Real.hasDerivAt_cos θ).const_mul r) using 1
    ring
  have he := intervalIntegral.integral_deriv_smul_comp
    (fun θ (_ : θ ∈ uIcc (0 : ℝ) Real.pi) => hd θ)
    (show ContinuousOn (fun θ => -r * Real.sin θ) (uIcc (0 : ℝ) Real.pi) by fun_prop) hg
  refine ⟨((NlsGge.Analysis.EllipseDeformation.velocity_continuous r 0).mul
    (hg.comp (by fun_prop))).intervalIntegrable 0 Real.pi,
    hg.intervalIntegrable (c + r) (c - r), ?_⟩
  simpa only [NlsGge.Analysis.EllipseDeformation.velocity, zero_mul, Complex.ofReal_zero, mul_zero,
    zero_add, add_zero, Real.cos_zero, Real.cos_pi, mul_one, mul_neg_one,
    ← sub_eq_add_neg, Function.comp_def, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_neg] using he

theorem flattened_upper_integral (u : PhysicalL2) (c r : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, NlsGge.Analysis.EllipseDeformation.velocity r 0 θ *
      NlsGge.GK38.ActionEllipseContinuity.upperPrimitive u (NlsGge.Analysis.EllipseDeformation.curve (c : ℂ) r 0 θ)) =
      ∫ x in (c + r)..(c - r), -Complex.I * actualQuasimomentumBoundaryE02_38 u x := by
  have h := (cosine_substitution
    (fun x => -Complex.I * actualQuasimomentumBoundaryE02_38 u x)
    (continuous_const.mul (continuous_actualQuasimomentumBoundaryE02_38 u)) c r).2.2
  convert h using 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [NlsGge.Analysis.EllipseDeformation.curve, NlsGge.GK38.ActionEllipseContinuity.upperPrimitive,
    actualQuasimomentumBoundaryE02_38, zero_mul, Complex.ofReal_zero, mul_zero,
    add_zero, Complex.ofReal_add, Complex.ofReal_mul]


theorem upperPrimitive_boundary_re (u : PhysicalL2) (x : ℝ) :
    (NlsGge.GK38.ActionEllipseContinuity.upperPrimitive u (x : ℂ)).re = actualGapHeightE02_38 u x := by
  calc
    _ = (actualQuasimomentumBoundaryE02_38 u x).im := by
      simp [NlsGge.GK38.ActionEllipseContinuity.upperPrimitive, actualQuasimomentumBoundaryE02_38,
        Complex.mul_re]
    _ = _ := boundaryLimit_im_E02_38 u x _ (tendsto_actualQuasimomentumBoundaryE02_38 u x)

theorem flattened_upper_integral_re (u : PhysicalL2) (c r : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, NlsGge.Analysis.EllipseDeformation.velocity r 0 θ *
      NlsGge.GK38.ActionEllipseContinuity.upperPrimitive u (NlsGge.Analysis.EllipseDeformation.curve (c : ℂ) r 0 θ)).re =
      -(∫ x in (c - r)..(c + r), actualGapHeightE02_38 u x) := by
  rw [flattened_upper_integral]
  have hi : IntervalIntegrable (fun x => -Complex.I * actualQuasimomentumBoundaryE02_38 u x)
      volume (c + r) (c - r) :=
    (continuous_const.mul (continuous_actualQuasimomentumBoundaryE02_38 u)).intervalIntegrable
      (c + r) (c - r)
  calc
    _ = ∫ x in (c + r)..(c - r), (-Complex.I * actualQuasimomentumBoundaryE02_38 u x).re :=
      (intervalIntegral.intervalIntegral_re hi).symm
    _ = ∫ x in (c + r)..(c - r), actualGapHeightE02_38 u x := by
      apply intervalIntegral.integral_congr
      intro x _
      exact upperPrimitive_boundary_re u x
    _ = _ := intervalIntegral.integral_symm _ _

end
end NlsGge.GK38.ActionEllipseCosine

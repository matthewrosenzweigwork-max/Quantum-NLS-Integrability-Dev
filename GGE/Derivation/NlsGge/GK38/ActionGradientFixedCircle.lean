import NlsGge.GK38.ActionGradientIntegrandVariation
import NlsGge.GK38.ActionGradientEvaluation

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.Pilot
namespace NlsGge.GK38.ActionGradient
noncomputable section

def actionPartial (φ : PotPair) (z : ℂ) : PotPair →L[ℂ] ℂ :=
  NlsGge.GK38.Lib.paramCircleDerivative38 actionIntegrand38 φ z

theorem actionPartial_joint_analytic :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => actionPartial p.1 p.2) rootDomain38 := by
  let F : PotPair × ℂ → ℂ := Function.uncurry actionIntegrand38
  let T : ((PotPair × ℂ) →L[ℂ] ℂ) →L[ℂ] (PotPair →L[ℂ] ℂ) :=
    (ContinuousLinearMap.compL ℂ PotPair (PotPair × ℂ) ℂ).flip
      (ContinuousLinearMap.inl ℂ PotPair ℂ)
  have he : (fun p : PotPair × ℂ => T (fderiv ℂ F p)) =
      (fun p : PotPair × ℂ => actionPartial p.1 p.2) := rfl
  rw [← he]
  intro p hp
  exact (T.analyticAt _).comp ((actionIntegrand_joint_analytic38 p hp).fderiv)

theorem actionPartial_circle_integrable (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    CircleIntegrable (actionPartial φ) (C n) (R n) := by
  have ha : AnalyticOnNhd ℂ (actionPartial φ) (actionCutDomain38 φ) := by
    intro z hz
    exact (actionPartial_joint_analytic (φ, z) ⟨hφ, hz⟩).comp
      ((analyticAt_const (v := φ)).prod analyticAt_id)
  exact (ha.continuousOn.mono (fixed_sphere_subset φ C R hf n)).circleIntegrable
    (isolating_radius_pos38 hf n).le

theorem circleIntegral_actionPartial_apply (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : IsolatingFamily38 φ C R) (n : ℤ) (h : PotPair) :
    (circleIntegral (actionPartial φ) (C n) (R n)) h =
      -circleIntegral (directionQuotient φ h) (C n) (R n) := by
  have hi := actionPartial_circle_integrable φ hφ C R hf n
  have hibp := gradient_circle_integration_by_parts φ hφ C R hf n h
  calc
    _ = circleIntegral (fun z => z * deriv (directionQuotient φ h) z) (C n) (R n) := by
      unfold circleIntegral
      rw [ContinuousLinearMap.intervalIntegral_apply hi.out h]
      apply intervalIntegral.integral_congr
      intro θ _
      change deriv (circleMap (C n) (R n)) θ * actionPartial φ (circleMap (C n) (R n) θ) h =
        deriv (circleMap (C n) (R n)) θ *
          (circleMap (C n) (R n) θ * deriv (directionQuotient φ h) (circleMap (C n) (R n) θ))
      exact congrArg (fun a : ℂ => deriv (circleMap (C n) (R n)) θ * a)
        (actionIntegrand_parameter_derivative φ (circleMap (C n) (R n) θ)
          ⟨hφ, fixed_sphere_subset φ C R hf n
            (circleMap_mem_sphere _ (isolating_radius_pos38 hf n).le θ)⟩ h)
    _ = _ := hibp.2.2

theorem fixed_contour_hasFDeriv (V : Set PotPair) (hVo : IsOpen V) (hVW : V ⊆ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hf : ∀ ψ ∈ V, IsolatingFamily38 ψ C R)
    (φ : PotPair) (hφV : φ ∈ V) (n : ℤ) :
    HasFDerivAt (fun ψ : PotPair => contourAction38 ψ (C n) (R n))
      (-(1 / (Real.pi : ℂ)) • circleIntegral (gradRootQuotient φ) (C n) (R n)) φ := by
  have hfamily := hf φ hφV
  have hφ := hVW hφV
  have hF := fixed_boundary_joint_analytic V C R hVW hf n
  have hi := actionPartial_circle_integrable φ hφ C R hfamily n
  have hq := gradRootQuotient_circle_integrable φ hφ C R hfamily n
  have hd := NlsGge.GK38.Lib.paramCircle_integral_hasFDerivAt38 hVo
    (isolating_radius_pos38 hfamily n) hF hφV
  change HasFDerivAt (fun ψ : PotPair => circleIntegral (actionIntegrand38 ψ) (C n) (R n))
    (∫ t in Icc 0 (2 * Real.pi), deriv (circleMap (C n) (R n)) t •
      actionPartial φ (circleMap (C n) (R n) t)) φ at hd
  rw [← circleIntegral_def_Icc (actionPartial φ) (C n) (R n)] at hd
  have he : (1 / (Real.pi : ℂ)) • circleIntegral (actionPartial φ) (C n) (R n) =
      -(1 / (Real.pi : ℂ)) • circleIntegral (gradRootQuotient φ) (C n) (R n) := by
    apply ContinuousLinearMap.ext
    intro h
    change (1 / (Real.pi : ℂ)) * (circleIntegral (actionPartial φ) (C n) (R n)) h =
      -(1 / (Real.pi : ℂ)) * (circleIntegral (gradRootQuotient φ) (C n) (R n)) h
    rw [circleIntegral_actionPartial_apply φ hφ C R hfamily n h,
      circleIntegral_gradRootQuotient_apply φ hφ C R hfamily n h]
    change (1 / (Real.pi : ℂ)) * (-circleIntegral (directionQuotient φ h) (C n) (R n)) =
      -(1 / (Real.pi : ℂ)) * circleIntegral (directionQuotient φ h) (C n) (R n)
    ring
  exact (hd.const_mul (1 / (Real.pi : ℂ))).congr_fderiv he

end
end NlsGge.GK38.ActionGradient

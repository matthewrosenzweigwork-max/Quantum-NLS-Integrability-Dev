import NlsGge.GK38.Lib.ParamCircleAnalyticBounds

/-! Analyticity of fixed-circle integrals in arbitrary complex Banach parameters.
We prove integrability, differentiate on a finite restricted interval, and use
the accepted scalar-line weak analyticity criterion to obtain Banach analyticity. -/

set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology

namespace NlsGge.GK38.Lib
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual parameter derivative of a fixed-circle integral, constructed
after integrability and a common compact-circle derivative bound. -/
theorem paramCircle_integral_hasFDerivAt38 {V : Set E} {c : ℂ} {r : ℝ}
    {F : E → ℂ → ℂ} (hV : IsOpen V) (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ (Function.uncurry F) (V ×ˢ sphere c r))
    {x₀ : E} (hx₀ : x₀ ∈ V) :
    HasFDerivAt (fun x => circleIntegral (F x) c r)
      (∫ t in Icc 0 (2 * Real.pi), deriv (circleMap c r) t •
        paramCircleDerivative38 F x₀ (circleMap c r t)) x₀ := by
  have hcircle := paramCircle_integrable38 hr hF hx₀
  obtain ⟨ε, hε, B, hB, hsub, hb⟩ := paramCircle_common_bound38 hV hF hx₀
  let μ : Measure ℝ := volume.restrict (Icc 0 (2 * Real.pi))
  let G : E → ℝ → ℂ := fun x t => deriv (circleMap c r) t • F x (circleMap c r t)
  let G' : E → ℝ → E →L[ℂ] ℂ := fun x t =>
    deriv (circleMap c r) t • paramCircleDerivative38 F x (circleMap c r t)
  have ha : Continuous (fun t => deriv (circleMap c r) t) := by
    simp only [deriv_circleMap]; fun_prop
  have hG : ∀ x ∈ V, Continuous (G x) := by
    intro x hx
    have hv : Continuous (fun t => F x (circleMap c r t)) :=
      hF.continuousOn.comp_continuous
        (by fun_prop : Continuous (fun t : ℝ => (x, circleMap c r t)))
        (fun t => ⟨hx, circleMap_mem_sphere c hr.le t⟩)
    exact ha.smul hv
  have hJ : Continuous (fun t => fderiv ℂ (Function.uncurry F) (x₀, circleMap c r t)) :=
    hF.fderiv.continuousOn.comp_continuous (by fun_prop)
      (fun t => ⟨hx₀, circleMap_mem_sphere c hr.le t⟩)
  have hG' : Continuous (G' x₀) := by
    dsimp [G', paramCircleDerivative38]
    fun_prop
  have hm : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (G x) μ := by
    filter_upwards [ball_mem_nhds x₀ hε] with x hx
    exact (hG x (hsub hx)).continuousOn.aestronglyMeasurable_of_isCompact
      isCompact_Icc measurableSet_Icc
  have hi : Integrable (G x₀) μ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le).mp hcircle.out
  have hmi : AEStronglyMeasurable (G' x₀) μ :=
    hG'.continuousOn.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc
  have hbound : ∀ᵐ t ∂μ, ∀ x ∈ ball x₀ ε, ‖G' x t‖ ≤ r * B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t _ht
    intro x hx
    have hz := circleMap_mem_sphere c hr.le t
    have hJnorm := (hb x hx _ hz).2.2
    have hD : ‖paramCircleDerivative38 F x (circleMap c r t)‖ ≤ B := by
      calc
        _ ≤ ‖fderiv ℂ (Function.uncurry F) (x, circleMap c r t)‖ *
            ‖ContinuousLinearMap.inl ℂ E ℂ‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ B * 1 := mul_le_mul hJnorm (ContinuousLinearMap.norm_inl_le_one ℂ E ℂ)
          (norm_nonneg _) hB
        _ = B := mul_one B
    have hanorm : ‖deriv (circleMap c r) t‖ = r := by
      simp [deriv_circleMap, abs_of_pos hr]
    dsimp [G']; rw [norm_smul, hanorm]
    exact mul_le_mul_of_nonneg_left hD hr.le
  have hbi : Integrable (fun _t : ℝ => r * B) μ := integrable_const _
  have hdi : Integrable (G' x₀) μ := Integrable.mono' hbi hmi
    (hbound.mono fun _t ht => ht x₀ (mem_ball_self hε))
  have hdiff : ∀ᵐ t ∂μ, ∀ x ∈ ball x₀ ε, HasFDerivAt (fun y => G y t) (G' x t) x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t _ht
    intro x hx
    exact (paramCircle_hasFDerivAt38
      (hb x hx _ (circleMap_mem_sphere c hr.le t)).1).const_smul (deriv (circleMap c r) t)
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (ball_mem_nhds x₀ hε) hm hi hmi hbound hbi hdiff
  simpa only [G, G', μ, ← circleIntegral_def_Icc] using hd

/-- Exact D4 generic contract: genuine integrability and analyticity of the
fixed-circle integral on an arbitrary complex Banach parameter domain. -/
theorem parametricCircleAnalytic38 (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (V : Set E) (c : ℂ) (r : ℝ) (F : E → ℂ → ℂ)
    (hV : IsOpen V) (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ (Function.uncurry F) (V ×ˢ sphere c r)) :
    (∀ x ∈ V, CircleIntegrable (F x) c r) ∧
      AnalyticOnNhd ℂ (fun x => circleIntegral (F x) c r) V := by
  refine ⟨fun x hx => paramCircle_integrable38 hr hF hx,
    analyticOnNhd_of_differentiableOn hV ?_⟩
  intro x hx
  exact (paramCircle_integral_hasFDerivAt38 hV hr hF hx).differentiableAt.differentiableWithinAt

end
end NlsGge.GK38.Lib

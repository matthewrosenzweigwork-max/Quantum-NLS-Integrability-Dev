import NlsGge.GK38.XiSqActualKernelBound

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- The reference Cauchy kernel has the exact A5 normalization; its integrability is earned first. -/
theorem a5ReferenceKernel_integral38 (c : ℂ) (r : ℝ) (hr : 0 < r) :
    CircleIntegrable (fun z => -1/(8*Complex.I*(c-z))) c r ∧
      (4/(Real.pi:ℂ))*circleIntegral (fun z => -1/(8*Complex.I*(c-z))) c r = 1 := by
  have hne (z : ℂ) (hz : z ∈ sphere c r) : c-z ≠ 0 := by
    intro he
    have he' : z=c := (sub_eq_zero.mp he).symm
    rw [he',mem_sphere_iff_norm,sub_self,norm_zero] at hz
    linarith
  have ha : AnalyticOnNhd ℂ (fun z => -1/(8*Complex.I*(c-z))) (sphere c r) := by
    intro z hz
    exact analyticAt_const.div (analyticAt_const.mul (analyticAt_const.sub analyticAt_id))
      (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (hne z hz))
  refine ⟨ContinuousOn.circleIntegrable hr.le ha.continuousOn, ?_⟩
  have he : circleIntegral (fun z => -1/(8*Complex.I*(c-z))) c r =
      (1/(8*Complex.I))*circleIntegral (fun z => (z-c)⁻¹) c r := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hzn : z-c ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (hne z hz)))
    field_simp [hne z hz,hzn]
    ring
  rw [he,circleIntegral.integral_sub_center_inv c hr.ne']
  field_simp
  norm_num

/-- A genuine circle-integrable kernel error gives the exact normalized error bound. -/
theorem a5NormalizedCircle_error38 (f : ℂ → ℂ) (c : ℂ) (r b : ℝ)
    (hr : 0 < r) (hi : CircleIntegrable f c r)
    (hbound : ∀ z ∈ sphere c r, ‖f z-(-1/(8*Complex.I*(c-z)))‖ ≤ b) :
    ‖(4/(Real.pi:ℂ))*circleIntegral f c r-1‖ ≤ 8*r*b := by
  obtain ⟨hif,hfree⟩ := a5ReferenceKernel_integral38 c r hr
  rw [← hfree,← mul_sub,← circleIntegral.integral_sub hi hif,norm_mul]
  have hn : ‖(4/(Real.pi:ℂ))‖ = 4/Real.pi := by
    rw [Complex.norm_div,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  rw [hn]
  calc
    _ ≤ (4/Real.pi)*(2*Real.pi*r*b) :=
      mul_le_mul_of_nonneg_left (circleIntegral.norm_integral_le_of_norm_le_const hr.le hbound)
        (by positivity)
    _ = _ := by field_simp; ring

end
end NlsGge.GK38

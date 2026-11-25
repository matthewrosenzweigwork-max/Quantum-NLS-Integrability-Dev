import Mathlib

/-!
# A Cauchy majorant for squared coordinates

The scalar estimate used by E01 L4c part 2c applies Cauchy's formula to `f²`.
Its boundary norm is `‖f‖²`, so no infinite sum–integral interchange is needed.
All boundary integrability is established before invoking the integral formula.
-/

set_option autoImplicit false

open Metric Set MeasureTheory
open scoped Real

namespace NlsGge.GK38.Lib

noncomputable section

/-- The uniform Cauchy coefficient for the disc of radius `r` inside radius `R`. -/
def sqCauchyCoeff (R r : ℝ) : ℝ :=
  ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * (R * (R - r)⁻¹)

theorem sqCauchyCoeff_nonneg {R r : ℝ} (hR : 0 ≤ R) (hr : r < R) :
    0 ≤ sqCauchyCoeff R r := by
  unfold sqCauchyCoeff
  positivity

/-- The square of a holomorphic coordinate admits an integral majorant on a smaller disc. -/
theorem norm_sq_le_sqCauchyCoeff_integral (f : ℂ → ℂ) {R r : ℝ}
    (hR : 0 < R) (hr : r < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    {z : ℂ} (hz : ‖z‖ < r) :
    ‖f z‖ ^ 2 ≤ sqCauchyCoeff R r *
      ∫ t : ℝ in 0..2 * Real.pi, ‖f (circleMap 0 R t)‖ ^ 2 := by
  have hsep (t : ℝ) : R - r ≤ ‖circleMap 0 R t - z‖ := by
    have h := norm_sub_norm_le (circleMap 0 R t) z
    rw [norm_circleMap_zero, abs_of_pos hR] at h
    linarith
  have hne (t : ℝ) : circleMap 0 R t - z ≠ 0 := by
    have hp : 0 < ‖circleMap 0 R t - z‖ := lt_of_lt_of_le (sub_pos.mpr hr) (hsep t)
    exact norm_pos_iff.mp hp
  have hc : Continuous (fun t : ℝ => f (circleMap 0 R t)) :=
    hf.continuousOn.comp_continuous (continuous_circleMap 0 R)
      (fun t => circleMap_mem_closedBall 0 hR.le t)
  have hk : Continuous (fun t : ℝ => (circleMap 0 R t - z)⁻¹) :=
    ((continuous_circleMap 0 R).sub continuous_const).inv₀ hne
  have hi : IntervalIntegrable (fun t : ℝ => ‖f (circleMap 0 R t)‖ ^ 2)
      volume 0 (2 * Real.pi) := (hc.norm.pow 2).intervalIntegrable _ _
  have hd : Continuous (fun t : ℝ => deriv (circleMap 0 R) t) := by
    simp only [deriv_circleMap]
    fun_prop
  have hkernel : IntervalIntegrable (fun t : ℝ => deriv (circleMap 0 R) t •
      ((circleMap 0 R t - z)⁻¹ • (f (circleMap 0 R t)) ^ 2))
      volume 0 (2 * Real.pi) := (hd.smul (hk.smul (hc.pow 2))).intervalIntegrable _ _
  have hn : IntervalIntegrable (fun t : ℝ => ‖deriv (circleMap 0 R) t •
      ((circleMap 0 R t - z)⁻¹ • (f (circleMap 0 R t)) ^ 2)‖)
      volume 0 (2 * Real.pi) := hkernel.norm
  have hb (t : ℝ) : ‖deriv (circleMap 0 R) t •
      ((circleMap 0 R t - z)⁻¹ • (f (circleMap 0 R t)) ^ 2)‖ ≤
      (R * (R - r)⁻¹) * ‖f (circleMap 0 R t)‖ ^ 2 := by
    have hinv : ‖circleMap 0 R t - z‖⁻¹ ≤ (R - r)⁻¹ :=
      inv_anti₀ (sub_pos.mpr hr) (hsep t)
    simp only [norm_smul, norm_inv, norm_pow, deriv_circleMap, norm_mul,
      Complex.norm_I, norm_circleMap_zero, abs_of_pos hR, mul_one]
    calc R * (‖circleMap 0 R t - z‖⁻¹ * ‖f (circleMap 0 R t)‖ ^ 2)
        ≤ R * ((R - r)⁻¹ * ‖f (circleMap 0 R t)‖ ^ 2) := by
          gcongr
      _ = _ := by ring
  have hf2 : DiffContOnCl ℂ (fun w => f w ^ 2) (ball 0 R) :=
    ((hf.pow 2).differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
  have hzR : z ∈ ball (0 : ℂ) R := by simpa using hz.trans hr
  have hformula := hf2.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hzR
  calc ‖f z‖ ^ 2 = ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ w in C(0, R), (w - z)⁻¹ • f w ^ 2‖ := by
          rw [hformula, norm_pow]
    _ = ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
        ‖∮ w in C(0, R), (w - z)⁻¹ • f w ^ 2‖ := norm_smul _ _
    _ ≤ ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
        ∫ t : ℝ in 0..2 * Real.pi, ‖deriv (circleMap 0 R) t •
          ((circleMap 0 R t - z)⁻¹ • f (circleMap 0 R t) ^ 2)‖ := by
          gcongr
          exact intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le
    _ ≤ ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
        ∫ t : ℝ in 0..2 * Real.pi,
          (R * (R - r)⁻¹) * ‖f (circleMap 0 R t)‖ ^ 2 := by
          gcongr
          exact intervalIntegral.integral_mono_on Real.two_pi_pos.le hn
            (hi.const_mul _) (fun t _ => hb t)
    _ = _ := by rw [intervalIntegral.integral_const_mul, sqCauchyCoeff]; ring

end

end NlsGge.GK38.Lib

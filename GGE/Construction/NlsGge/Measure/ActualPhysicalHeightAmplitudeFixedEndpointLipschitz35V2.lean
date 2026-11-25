import NlsGge.Measure.ActualPhysicalBoundedHeightAmplitudeLp1Classes35V2
import NlsGge.Measure.ActualRealExponentialBoundedHeightLipschitz35V1

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis

/-- Pointwise fixed-endpoint height estimate for the actual 00 amplitude.
The right side is supported on the actual physical interval and retains the
actual conjugated source. -/
theorem actualPhysicalHeightAmplitude00_fixedEndpointLipschitz35V2
    (u : PhysicalL2) (s Y₀ Y Y' r : ℝ)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (hY₀ : 0 ≤ Y₀)
    (hY : Y ∈ Set.Icc (0 : ℝ) Y₀) (hY' : Y' ∈ Set.Icc (0 : ℝ) Y₀) :
    ‖actualPhysicalHeightAmplitude00_35V3 u s Y r -
        actualPhysicalHeightAmplitude00_35V3 u s Y' r‖ ≤
      Set.indicator (Set.Ioc (0 : ℝ) s)
        (fun x : ℝ => 2 * Real.exp (2 * Y₀) * |Y - Y'| *
          ‖actualPhysicalL2SourcePotential u x‖) r := by
  by_cases hr : r ∈ Set.Ioc (0 : ℝ) s
  · have hr0 : 0 ≤ r := le_of_lt hr.1
    have hr1 : r ≤ 1 := hr.2.trans hs₁
    have hYr : Y * r ≤ Y₀ := by
      calc
        Y * r ≤ Y₀ * r := mul_le_mul_of_nonneg_right hY.2 hr0
        _ ≤ Y₀ := by nlinarith [mul_le_mul_of_nonneg_left hr1 hY₀]
    have hY'r : Y' * r ≤ Y₀ := by
      calc
        Y' * r ≤ Y₀ * r := mul_le_mul_of_nonneg_right hY'.2 hr0
        _ ≤ Y₀ := by nlinarith [mul_le_mul_of_nonneg_left hr1 hY₀]
    have harg : 2 * Y * r ∈ Set.Icc (-2 * Y₀) (2 * Y₀) := by
      constructor <;> nlinarith [hY.1, hYr]
    have harg' : 2 * Y' * r ∈ Set.Icc (-2 * Y₀) (2 * Y₀) := by
      constructor <;> nlinarith [hY'.1, hY'r]
    have hexp := actualRealExp_boundedHeight_lipschitz35V1 Y₀
      (2 * Y * r) (2 * Y' * r) hY₀ harg harg'
    have hargdiff : |(2 * Y * r) - (2 * Y' * r)| ≤ 2 * |Y - Y'| := by
      rw [show (2 * Y * r) - (2 * Y' * r) = 2 * r * (Y - Y') by ring,
        abs_mul, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr0)]
      nlinarith [hr1, abs_nonneg (Y - Y')]
    have hpoint : |Real.exp (2 * Y * r) - Real.exp (2 * Y' * r)| ≤
        2 * Real.exp (2 * Y₀) * |Y - Y'| := by
      calc
        _ ≤ Real.exp (2 * Y₀) * |(2 * Y * r) - (2 * Y' * r)| := hexp
        _ ≤ Real.exp (2 * Y₀) * (2 * |Y - Y'|) :=
          mul_le_mul_of_nonneg_left hargdiff (Real.exp_nonneg _)
        _ = 2 * Real.exp (2 * Y₀) * |Y - Y'| := by ring
    have hnorm : ‖star (actualPhysicalL2SourcePotential u r)‖ =
        ‖actualPhysicalL2SourcePotential u r‖ := norm_star _
    have hdiffnorm :
        ‖Complex.exp ((2 * Y * r : ℝ) : ℂ) -
            Complex.exp ((2 * Y' * r : ℝ) : ℂ)‖ =
          |Real.exp (2 * Y * r) - Real.exp (2 * Y' * r)| := by
      change ‖Complex.exp ((2 * Y * r : ℝ) : ℂ) -
          Complex.exp ((2 * Y' * r : ℝ) : ℂ)‖ = _
      rw [← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
    simpa [actualPhysicalHeightAmplitude00_35V3, Set.indicator_of_mem, hr,
      hnorm] using
      (calc
        ‖star (actualPhysicalL2SourcePotential u r) *
              Complex.exp ((2 * Y * r : ℝ) : ℂ) -
            star (actualPhysicalL2SourcePotential u r) *
              Complex.exp ((2 * Y' * r : ℝ) : ℂ)‖
            = ‖actualPhysicalL2SourcePotential u r‖ *
                |Real.exp (2 * Y * r) - Real.exp (2 * Y' * r)| := by
                  rw [← mul_sub, norm_mul, norm_star, hdiffnorm]
        _ ≤ ‖actualPhysicalL2SourcePotential u r‖ *
              (2 * Real.exp (2 * Y₀) * |Y - Y'|) :=
                mul_le_mul_of_nonneg_left hpoint (norm_nonneg _)
        _ = 2 * Real.exp (2 * Y₀) * |Y - Y'| *
              ‖actualPhysicalL2SourcePotential u r‖ := by ring)
  · simp [actualPhysicalHeightAmplitude00_35V3, Set.indicator_of_notMem, hr]

/-- Pointwise fixed-endpoint height estimate for the actual 11 amplitude;
the physical source is unstarred and the height exponent has its original
opposite sign. -/
theorem actualPhysicalHeightAmplitude11_fixedEndpointLipschitz35V2
    (u : PhysicalL2) (s Y₀ Y Y' r : ℝ)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (hY₀ : 0 ≤ Y₀)
    (hY : Y ∈ Set.Icc (0 : ℝ) Y₀) (hY' : Y' ∈ Set.Icc (0 : ℝ) Y₀) :
    ‖actualPhysicalHeightAmplitude11_35V3 u s Y r -
        actualPhysicalHeightAmplitude11_35V3 u s Y' r‖ ≤
      Set.indicator (Set.Ioc (0 : ℝ) s)
        (fun x : ℝ => 2 * Real.exp (2 * Y₀) * |Y - Y'| *
          ‖actualPhysicalL2SourcePotential u x‖) r := by
  by_cases hr : r ∈ Set.Ioc (0 : ℝ) s
  · have hr0 : 0 ≤ r := le_of_lt hr.1
    have hr1 : r ≤ 1 := hr.2.trans hs₁
    have hYr : Y * r ≤ Y₀ := by
      calc
        Y * r ≤ Y₀ * r := mul_le_mul_of_nonneg_right hY.2 hr0
        _ ≤ Y₀ := by nlinarith [mul_le_mul_of_nonneg_left hr1 hY₀]
    have hY'r : Y' * r ≤ Y₀ := by
      calc
        Y' * r ≤ Y₀ * r := mul_le_mul_of_nonneg_right hY'.2 hr0
        _ ≤ Y₀ := by nlinarith [mul_le_mul_of_nonneg_left hr1 hY₀]
    have harg : -2 * Y * r ∈ Set.Icc (-2 * Y₀) (2 * Y₀) := by
      constructor <;> nlinarith [hY.1, hYr]
    have harg' : -2 * Y' * r ∈ Set.Icc (-2 * Y₀) (2 * Y₀) := by
      constructor <;> nlinarith [hY'.1, hY'r]
    have hexp := actualRealExp_boundedHeight_lipschitz35V1 Y₀
      (-2 * Y * r) (-2 * Y' * r) hY₀ harg harg'
    have hargdiff : |(-2 * Y * r) - (-2 * Y' * r)| ≤ 2 * |Y - Y'| := by
      rw [show (-2 * Y * r) - (-2 * Y' * r) = -2 * r * (Y - Y') by ring,
        abs_mul, abs_of_nonpos (by nlinarith [hr0])]
      nlinarith [hr1, abs_nonneg (Y - Y')]
    have hpoint : |Real.exp (-2 * Y * r) - Real.exp (-2 * Y' * r)| ≤
        2 * Real.exp (2 * Y₀) * |Y - Y'| := by
      calc
        _ ≤ Real.exp (2 * Y₀) * |(-2 * Y * r) - (-2 * Y' * r)| := hexp
        _ ≤ Real.exp (2 * Y₀) * (2 * |Y - Y'|) :=
          mul_le_mul_of_nonneg_left hargdiff (Real.exp_nonneg _)
        _ = 2 * Real.exp (2 * Y₀) * |Y - Y'| := by ring
    have hdiffnorm :
        ‖Complex.exp ((-2 * Y * r : ℝ) : ℂ) -
            Complex.exp ((-2 * Y' * r : ℝ) : ℂ)‖ =
          |Real.exp (-2 * Y * r) - Real.exp (-2 * Y' * r)| := by
      change ‖Complex.exp ((-2 * Y * r : ℝ) : ℂ) -
          Complex.exp ((-2 * Y' * r : ℝ) : ℂ)‖ = _
      rw [← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
    simpa [actualPhysicalHeightAmplitude11_35V3, Set.indicator_of_mem, hr] using
      (calc
        ‖actualPhysicalL2SourcePotential u r *
              Complex.exp ((-2 * Y * r : ℝ) : ℂ) -
            actualPhysicalL2SourcePotential u r *
              Complex.exp ((-2 * Y' * r : ℝ) : ℂ)‖
            = ‖actualPhysicalL2SourcePotential u r‖ *
                |Real.exp (-2 * Y * r) - Real.exp (-2 * Y' * r)| := by
                  rw [← mul_sub, norm_mul, hdiffnorm]
        _ ≤ ‖actualPhysicalL2SourcePotential u r‖ *
              (2 * Real.exp (2 * Y₀) * |Y - Y'|) :=
                mul_le_mul_of_nonneg_left hpoint (norm_nonneg _)
        _ = 2 * Real.exp (2 * Y₀) * |Y - Y'| *
              ‖actualPhysicalL2SourcePotential u r‖ := by ring)
  · simp [actualPhysicalHeightAmplitude11_35V3, Set.indicator_of_notMem, hr]

end NlsGge.SpectralFoundations
end

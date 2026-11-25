import QuantumNLS.TerraMultiRound75FractionalKernel
import Mathlib.MeasureTheory.Integral.Prod

/-! Tonelli lift of the scalar fractional kernel to arbitrary s-finite
spectral measures, including infinite moments. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace QuantumNLS.TerraMultiRound76ExtendedKernel

/-- Positive-kernel representation of an extended fractional moment. The
normalization is an explicit positive integral and the kernel parameter is
the square of the printed Y variable. -/
theorem low_extended_moment (μ : Measure ℝ) [SFinite μ] (s : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) :
    let C : ℝ := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1
    ENNReal.ofReal C * (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2*s)) ∂μ) =
      ∫⁻ t in Ioi 0, ∫⁻ x : ℝ, ENNReal.ofReal (Real.rpowIntegrand₀₁ s t (x^2)) ∂μ := by
  let C : ℝ := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1
  have hp : s ∈ Ioo (0 : ℝ) 1 := ⟨hs0, hs1⟩
  have hC : 0 ≤ C := (Real.integral_rpowIntegrand₀₁_one_pos hp).le
  have hmeas : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (Real.rpowIntegrand₀₁ s z.1 (z.2^2))) := by
    unfold Real.rpowIntegrand₀₁
    fun_prop
  change ENNReal.ofReal C * (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2*s)) ∂μ) = _
  rw [← lintegral_const_mul _ (by fun_prop)]
  calc
    (∫⁻ x : ℝ, ENNReal.ofReal C * ENNReal.ofReal (|x| ^ (2*s)) ∂μ) =
        ∫⁻ x : ℝ, ∫⁻ t : ℝ, ENNReal.ofReal (Real.rpowIntegrand₀₁ s t (x^2)) ∂(volume.restrict (Ioi 0)) ∂μ := by
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul hC]
      have heq : C * |x| ^ (2*s) = ∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t (x^2) := by
        have h := Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hp (sq_nonneg x)
        have hx : (x^2)^s = |x| ^ (2*s) := by
          rw [Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]
        rw [hx] at h
        dsimp [C]
        linarith
      rw [heq, ofReal_integral_eq_lintegral_ofReal (Real.integrableOn_rpowIntegrand₀₁_Ioi hp (sq_nonneg x))]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpowIntegrand₀₁_nonneg hs0 ht.le (sq_nonneg x)
    _ = ∫⁻ t in Ioi 0, ∫⁻ x : ℝ, ENNReal.ofReal (Real.rpowIntegrand₀₁ s t (x^2)) ∂μ := by
      symm
      exact lintegral_lintegral_swap (f := fun t x => ENNReal.ofReal (Real.rpowIntegrand₀₁ s t (x^2))) hmeas.aemeasurable

/-- The upper-order positive representation, valid without assuming that the
second or the fractional moment is finite. -/
theorem upper_extended_moment (μ : Measure ℝ) [SFinite μ] (s : ℝ)
    (hs1 : 1 < s) (hs2 : s < 2) :
    let C : ℝ := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1
    ENNReal.ofReal C * (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2*s)) ∂μ) =
      ∫⁻ t in Ioi 0, ∫⁻ x : ℝ, ENNReal.ofReal (x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2)) ∂μ := by
  let C : ℝ := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s-1) t 1
  have hp : s-1 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hC : 0 ≤ C := (Real.integral_rpowIntegrand₀₁_one_pos hp).le
  have hmeas : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal
      (z.2^2 * Real.rpowIntegrand₀₁ (s-1) z.1 (z.2^2))) := by
    unfold Real.rpowIntegrand₀₁
    fun_prop
  change ENNReal.ofReal C * (∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2*s)) ∂μ) = _
  rw [← lintegral_const_mul _ (by fun_prop)]
  calc
    (∫⁻ x : ℝ, ENNReal.ofReal C * ENNReal.ofReal (|x| ^ (2*s)) ∂μ) =
        ∫⁻ x : ℝ, ∫⁻ t : ℝ, ENNReal.ofReal (x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2)) ∂(volume.restrict (Ioi 0)) ∂μ := by
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul hC]
      have heq : C * |x| ^ (2*s) = ∫ t in Ioi 0, x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2) := by
        rw [integral_const_mul]
        have h := Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hp (sq_nonneg x)
        have hpow : |x| ^ (2*s) = (x^2) ^ (s-1) * x^2 := by
          have h₁ := Real.rpow_add' (y := s-1) (z := 1) (sq_nonneg x) (by linarith)
          have h₂ : |x| ^ (2*s) = (x^2)^s := by
            rw [Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]
          rw [h₂]
          simpa only [sub_add_cancel, Real.rpow_one] using h₁
        rw [hpow, h]
        dsimp [C]
        ring
      rw [heq, ofReal_integral_eq_lintegral_ofReal
        ((Real.integrableOn_rpowIntegrand₀₁_Ioi hp (sq_nonneg x)).const_mul (x^2))]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (sq_nonneg x) (Real.rpowIntegrand₀₁_nonneg hp.1 ht.le (sq_nonneg x))
    _ = ∫⁻ t in Ioi 0, ∫⁻ x : ℝ, ENNReal.ofReal (x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2)) ∂μ := by
      symm
      exact lintegral_lintegral_swap (f := fun t x => ENNReal.ofReal (x^2 * Real.rpowIntegrand₀₁ (s-1) t (x^2))) hmeas.aemeasurable

#print axioms upper_extended_moment
#print axioms low_extended_moment
end QuantumNLS.TerraMultiRound76ExtendedKernel

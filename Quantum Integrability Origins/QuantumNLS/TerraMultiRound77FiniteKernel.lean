import QuantumNLS.TerraMultiRound76PhysicalKernels
import QuantumNLS.Reg010LowBasic

/-! Fubini for finite fractional moments. The normalization is kept as the
positive scalar integral; no subtraction of extended moments is used. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound77FiniteKernel

/-- The squared-parameter kernel is jointly integrable whenever the power
moment is finite. -/
theorem low_kernel_product_integrable (μ : Measure ℝ) [SFinite μ]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hm : Integrable (fun x : ℝ => |x| ^ (2*s)) μ) :
    Integrable (fun z : ℝ × ℝ => Real.rpowIntegrand₀₁ s z.1 (z.2^2))
      ((volume.restrict (Ioi 0)).prod μ) := by
  let C : ℝ := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1
  have hp : s ∈ Ioo (0 : ℝ) 1 := ⟨hs0, hs1⟩
  have hmeas : Measurable (fun z : ℝ × ℝ => Real.rpowIntegrand₀₁ s z.1 (z.2^2)) := by
    unfold Real.rpowIntegrand₀₁
    fun_prop
  apply (integrable_prod_iff' hmeas.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (fun x => Real.integrableOn_rpowIntegrand₀₁_Ioi hp (sq_nonneg x))
  · have heq : (fun x : ℝ => ∫ t in Ioi 0, ‖Real.rpowIntegrand₀₁ s t (x^2)‖) =
        fun x => C * |x| ^ (2*s) := by
      funext x
      have hnorm : (∫ t in Ioi 0, ‖Real.rpowIntegrand₀₁ s t (x^2)‖) =
          ∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t (x^2) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpowIntegrand₀₁_nonneg hs0 ht.le (sq_nonneg x))]
      rw [hnorm]
      have h := Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hp (sq_nonneg x)
      have hx : (x^2)^s = |x| ^ (2*s) := by
        rw [Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]
      rw [hx] at h
      dsimp [C]
      linarith
    rw [heq]
    exact hm.const_mul C

/-- Fubini identifies the finite power moment with the integral of its
positive spectral regularization. -/
theorem low_finite_moment (μ : Measure ℝ) [SFinite μ]
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hm : Integrable (fun x : ℝ => |x| ^ (2*s)) μ) :
    (∫ t in Ioi 0, ∫ x : ℝ, Real.rpowIntegrand₀₁ s t (x^2) ∂μ) =
      (∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1) * (∫ x : ℝ, |x| ^ (2*s) ∂μ) := by
  have hi := low_kernel_product_integrable μ s hs0 hs1 hm
  rw [integral_integral_swap hi]
  have hp : s ∈ Ioo (0 : ℝ) 1 := ⟨hs0, hs1⟩
  have heq : (fun x : ℝ => ∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t (x^2)) =
      fun x => (∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1) * |x| ^ (2*s) := by
    funext x
    have h := Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hp (sq_nonneg x)
    have hx : (x^2)^s = |x| ^ (2*s) := by
      rw [Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]
    rw [hx] at h
    linarith
  rw [heq, integral_const_mul]

#print axioms low_kernel_product_integrable
#print axioms low_finite_moment
end QuantumNLS.TerraMultiRound77FiniteKernel

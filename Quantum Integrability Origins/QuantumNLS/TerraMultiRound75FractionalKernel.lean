import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-! Positive fractional scalar kernels in the squared spectral parameter. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound75FractionalKernel

/-- The low-order positive scalar formula, written with the squared spectral
parameter. Its normalizing integral is strictly positive. -/
theorem low_kernel (s x : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    let C := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1
    0 < C ∧ |x| ^ (2 * s) = C⁻¹ *
      ∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t (x ^ 2) := by
  have hp : s ∈ Ioo (0 : ℝ) 1 := ⟨hs0, hs1⟩
  refine ⟨Real.integral_rpowIntegrand₀₁_one_pos hp, ?_⟩
  have h := Real.rpow_eq_const_mul_integral hp (sq_nonneg x)
  have heq : |x| ^ (2 * s) = (x ^ 2) ^ s := by
    rw [Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]
  exact heq.trans h

/-- The upper-order scalar formula uses the same positive kernel multiplied
by the second spectral moment; it is valid at zero as well. -/
theorem upper_kernel (s x : ℝ) (hs1 : 1 < s) (hs2 : s < 2) :
    let C := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ (s - 1) t 1
    0 < C ∧ |x| ^ (2 * s) = C⁻¹ *
      ∫ t in Ioi 0, (x ^ 2 * Real.rpowIntegrand₀₁ (s - 1) t (x ^ 2)) := by
  have hp : s - 1 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  refine ⟨Real.integral_rpowIntegrand₀₁_one_pos hp, ?_⟩
  have h := Real.rpow_eq_const_mul_integral hp (sq_nonneg x)
  have hpow : (x ^ 2) ^ s = (x ^ 2) ^ (s - 1) * x ^ 2 := by
    have h := Real.rpow_add' (y := s - 1) (z := 1) (sq_nonneg x) (by linarith)
    simpa only [sub_add_cancel, Real.rpow_one] using h
  have heq : |x| ^ (2 * s) = (x ^ 2) ^ s := by
    rw [Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]
  rw [heq, hpow, h, integral_const_mul]
  ring

#print axioms low_kernel
#print axioms upper_kernel
end QuantumNLS.TerraMultiRound75FractionalKernel

import QuantumNLS.TerraMultiRound60KernelBound

/-! Finite integral recurrence for regularized even moments. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound61MomentRecurrence
open QuantumNLS.TerraMultiRound60Kernel

theorem kernel_le_moment (s : ℕ) (Y t : ℝ) (hY : 0 < Y) :
    kernel s Y t ≤ t ^ (2 * s) := by
  have hd : 0 < Y^2 + t^2 := by positivity
  have hp : 0 ≤ t ^ (2*s) := (even_two_mul s).pow_nonneg t
  unfold kernel
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg hp (sq_nonneg t)]

theorem kernel_integrable (μ : Measure ℝ) (s : ℕ) (Y : ℝ) (hY : 0 < Y)
    (hm : Integrable (fun t : ℝ => t ^ (2*s)) μ) :
    Integrable (kernel s Y) μ := by
  apply hm.mono'
  · apply Continuous.aestronglyMeasurable
    unfold kernel
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg s Y t)]
    exact kernel_le_moment s Y t hY

theorem kernel_integrable_succ (μ : Measure ℝ) (s : ℕ) (Y : ℝ) (hY : 0 < Y)
    (hm : Integrable (fun t : ℝ => t ^ (2*s)) μ) :
    Integrable (kernel (s+1) Y) μ := by
  apply (hm.const_mul (Y^2)).mono'
  · apply Continuous.aestronglyMeasurable
    unfold kernel
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg (s+1) Y t)]
    exact kernel_le_previous s Y t hY

theorem integral_recurrence (μ : Measure ℝ) (s : ℕ) (Y : ℝ) (hY : 0 < Y)
    (hm : Integrable (fun t : ℝ => t ^ (2*s)) μ) :
    (∫ t, kernel (s+1) Y t ∂μ) =
      Y^2 * (∫ t : ℝ, t ^ (2*s) ∂μ) - Y^2 * (∫ t, kernel s Y t ∂μ) := by
  simp_rw [kernel_succ s Y _ hY]
  rw [integral_sub (hm.const_mul _) ((kernel_integrable μ s Y hY hm).const_mul _),
    integral_const_mul, integral_const_mul]

#print axioms kernel_le_moment
#print axioms kernel_integrable
#print axioms kernel_integrable_succ
#print axioms integral_recurrence
end QuantumNLS.TerraMultiRound61MomentRecurrence

import QuantumNLS.TerraMultiRound61MomentRecurrence

/-! Finite leading moments pass to the limit in regularized differences. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
namespace QuantumNLS.TerraMultiRound62FiniteLimit
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound60KernelLimit
open QuantumNLS.TerraMultiRound61MomentRecurrence

theorem integral_kernel_tendsto (μ : Measure ℝ) (s : ℕ)
    (hm : Integrable (fun t : ℝ => t^(2*s)) μ) :
    Tendsto (fun Y : ℝ => ∫ t, kernel s Y t ∂μ) atTop
      (𝓝 (∫ t : ℝ, t^(2*s) ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => t^(2*s))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    exact (kernel_integrable μ s Y hY hm).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    exact ae_of_all μ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg s Y t)]
      exact kernel_le_moment s Y t hY
  · exact hm
  · exact ae_of_all μ (kernel_tendsto s)

theorem difference_tendsto (μ ν : Measure ℝ) (s : ℕ)
    (hμ : Integrable (fun t : ℝ => t^(2*s)) μ)
    (hν : Integrable (fun t : ℝ => t^(2*s)) ν) :
    Tendsto (fun Y : ℝ => (∫ t, kernel s Y t ∂μ) - (∫ t, kernel s Y t ∂ν)) atTop
      (𝓝 ((∫ t : ℝ, t^(2*s) ∂μ) - (∫ t : ℝ, t^(2*s) ∂ν))) :=
  (integral_kernel_tendsto μ s hμ).sub (integral_kernel_tendsto ν s hν)

#print axioms integral_kernel_tendsto
#print axioms difference_tendsto
end QuantumNLS.TerraMultiRound62FiniteLimit

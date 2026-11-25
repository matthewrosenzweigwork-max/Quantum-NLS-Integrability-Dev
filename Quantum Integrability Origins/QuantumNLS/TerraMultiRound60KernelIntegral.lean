import QuantumNLS.TerraMultiRound60KernelLimit

/-! Monotone convergence of regularized moments for an arbitrary positive measure. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open scoped ENNReal
namespace QuantumNLS.TerraMultiRound60KernelIntegral
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound60KernelLimit

theorem kernel_lintegral_tendsto (μ : Measure ℝ) (s : ℕ) :
    Tendsto (fun n : ℕ => ∫⁻ t, ENNReal.ofReal (kernel s ((n : ℝ)+1) t) ∂μ)
      atTop (𝓝 (∫⁻ t, ENNReal.ofReal (t^(2*s)) ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    apply Measurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp
    unfold kernel
    fun_prop
  · apply ae_of_all
    intro t i j hij
    apply ENNReal.ofReal_le_ofReal
    apply kernel_mono
    · positivity
    · have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
  · apply ae_of_all
    intro t
    apply ENNReal.tendsto_ofReal
    apply (kernel_tendsto s t).comp
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

#print axioms kernel_lintegral_tendsto
end QuantumNLS.TerraMultiRound60KernelIntegral

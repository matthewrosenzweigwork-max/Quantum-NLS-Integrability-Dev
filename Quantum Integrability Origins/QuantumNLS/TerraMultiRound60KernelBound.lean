import QuantumNLS.TerraMultiRound60KernelIntegral

/-! Finite lower moments control every regularized higher moment. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open scoped ENNReal
namespace QuantumNLS.TerraMultiRound60KernelBound
open QuantumNLS.TerraMultiRound60Kernel

theorem kernel_lintegral_le (μ : Measure ℝ) (s : ℕ) (Y : ℝ) (hY : 0 < Y) :
    (∫⁻ t, ENNReal.ofReal (kernel (s+1) Y t) ∂μ) ≤
      ENNReal.ofReal (Y^2) * ∫⁻ t, ENNReal.ofReal (t^(2*s)) ∂μ := by
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (Y^2 * t^(2*s)) ∂μ :=
      lintegral_mono fun t => ENNReal.ofReal_le_ofReal (kernel_le_previous s Y t hY)
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (sq_nonneg Y)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem kernel_lintegral_ne_top (μ : Measure ℝ) (s : ℕ) (Y : ℝ) (hY : 0 < Y)
    (hfinite : (∫⁻ t, ENNReal.ofReal (t^(2*s)) ∂μ) ≠ ⊤) :
    (∫⁻ t, ENNReal.ofReal (kernel (s+1) Y t) ∂μ) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (kernel_lintegral_le μ s Y hY)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite

#print axioms kernel_lintegral_le
#print axioms kernel_lintegral_ne_top
end QuantumNLS.TerraMultiRound60KernelBound

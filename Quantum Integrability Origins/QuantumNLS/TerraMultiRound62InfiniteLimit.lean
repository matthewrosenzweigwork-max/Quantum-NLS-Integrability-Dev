import QuantumNLS.TerraMultiRound62FiniteLimit

/-! Infinite leading moments diverge, even after subtracting a finite one. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open scoped ENNReal
namespace QuantumNLS.TerraMultiRound62InfiniteLimit
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound60KernelIntegral
open QuantumNLS.TerraMultiRound61MomentRecurrence QuantumNLS.TerraMultiRound62FiniteLimit

theorem infinite_integral_kernel (μ : Measure ℝ) (s : ℕ)
    (hlower : Integrable (fun t : ℝ => t^(2*s)) μ)
    (hinf : (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*(s+1))) ∂μ) = ⊤) :
    Tendsto (fun n : ℕ => ∫ t, kernel (s+1) ((n : ℝ)+1) t ∂μ) atTop atTop := by
  apply ENNReal.tendsto_ofReal_nhds_top.mp
  have h := kernel_lintegral_tendsto μ (s+1)
  rw [hinf] at h
  apply h.congr'
  filter_upwards with n
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  exact (ofReal_integral_eq_lintegral_ofReal (kernel_integrable_succ μ s _ hpos hlower)
    (ae_of_all μ (kernel_nonneg (s+1) _))).symm

theorem infinite_difference (μ ν : Measure ℝ) (s : ℕ)
    (hlower : Integrable (fun t : ℝ => t^(2*s)) μ)
    (hinf : (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*(s+1))) ∂μ) = ⊤)
    (hν : Integrable (fun t : ℝ => t^(2*(s+1))) ν) :
    Tendsto (fun n : ℕ => (∫ t, kernel (s+1) ((n : ℝ)+1) t ∂μ) -
      (∫ t, kernel (s+1) ((n : ℝ)+1) t ∂ν)) atTop atTop := by
  have hμ := infinite_integral_kernel μ s hlower hinf
  have hνlim := (integral_kernel_tendsto ν (s+1) hν).comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hb : ∀ᶠ n : ℕ in atTop,
      (∫ t, kernel (s+1) ((n : ℝ)+1) t ∂ν) ≤ (∫ t : ℝ, t^(2*(s+1)) ∂ν) + 1 := by
    exact (hνlim.eventually (eventually_lt_nhds (by linarith))).mono fun _ hn => le_of_lt hn
  have hshift := tendsto_atTop_add_const_right atTop
    (-((∫ t : ℝ, t^(2*(s+1)) ∂ν) + 1)) hμ
  apply tendsto_atTop_mono' atTop _ hshift
  filter_upwards [hb] with n hn
  linarith

#print axioms infinite_integral_kernel
#print axioms infinite_difference
end QuantumNLS.TerraMultiRound62InfiniteLimit

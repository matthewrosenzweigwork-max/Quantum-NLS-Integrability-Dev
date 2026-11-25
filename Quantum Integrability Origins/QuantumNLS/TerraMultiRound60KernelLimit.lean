import QuantumNLS.TerraMultiRound60Kernel

/-! Pointwise convergence of the regularized even-moment kernels. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace QuantumNLS.TerraMultiRound60KernelLimit
open QuantumNLS.TerraMultiRound60Kernel

theorem kernel_tendsto (s : ℕ) (t : ℝ) :
    Tendsto (fun Y : ℝ => kernel s Y t) atTop (𝓝 (t^(2*s))) := by
  have hd : Tendsto (fun Y : ℝ => Y^2 + t^2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (t^2) (tendsto_pow_atTop two_ne_zero)
  have h : Tendsto (fun Y : ℝ => t^(2*s) - t^(2*s+2) / (Y^2+t^2))
      atTop (𝓝 (t^(2*s) - 0)) := tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hd :
    Tendsto (fun Y : ℝ => t^(2*s+2) / (Y^2+t^2)) atTop (𝓝 0))
  have he : ∀ᶠ Y : ℝ in atTop,
      kernel s Y t = t^(2*s) - t^(2*s+2)/(Y^2+t^2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    have hne : Y^2+t^2 ≠ 0 := by positivity
    unfold kernel
    rw [pow_add]
    field_simp
    <;> ring
  simpa only [sub_zero] using h.congr' (he.mono fun _ hx => hx.symm)

#print axioms kernel_tendsto
end QuantumNLS.TerraMultiRound60KernelLimit

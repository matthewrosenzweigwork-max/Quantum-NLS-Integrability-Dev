import QuantumNLS.KernelConvergence

/-! A norm squeeze for a vanishing scalar multiplying bounded varying terms. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace QuantumNLS.TerraMultiRound20NormLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem vanishing_smul_of_norm_bound (c a b : ℕ → ℝ) (K : ℕ → E)
    (a₀ b₀ : ℝ)
    (hc : Tendsto c atTop (𝓝 0)) (hcn : ∀ n, 0 ≤ c n)
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (hK : ∀ n, ‖K n‖ ≤ a n * b n) :
    Tendsto (fun n => (c n : ℂ) • K n) atTop (𝓝 0) := by
  have hm : Tendsto (fun n => c n * (a n * b n)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hc.mul (ha.mul hb)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hm
  apply Eventually.of_forall
  intro n
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcn n)]
  exact mul_le_mul_of_nonneg_left (hK n) (hcn n)

#print axioms vanishing_smul_of_norm_bound
end QuantumNLS.TerraMultiRound20NormLimit

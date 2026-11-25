import QuantumNLS.TerraMultiRound46Truncation
import QuantumNLS.TerraMultiRound56FiniteRemainder

/-! The geometric truncation majorant is of strictly smaller order than the
last retained inverse power. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound57Tail

/-- The denominator of a geometric majorant is harmless at inverse scale zero. -/
theorem geometric_majorant_littleO (A B : ℝ) (s : ℕ) :
    (fun Y : ℝ => A * (Y⁻¹ * (B * Y⁻¹ ^ 2) ^ (s + 1) *
      (1 - B * Y⁻¹ ^ 2)⁻¹)) =o[atTop]
      (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1)) := by
  have hz : Tendsto (fun Y : ℝ => Y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hd : Tendsto (fun Y : ℝ => (1 - B * Y⁻¹ ^ 2)⁻¹) atTop (𝓝 1) := by
    have h : Tendsto (fun Y : ℝ => 1 - B * Y⁻¹ ^ 2) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul (hz.pow 2))
    simpa using h.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hp : (fun Y : ℝ => Y⁻¹ ^ (2 * (s + 1) + 1)) =o[atTop]
      (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1)) := by
    exact (isLittleO_pow_pow (𝕜 := ℝ) (by omega : 2 * s + 1 < 2 * (s + 1) + 1)).comp_tendsto hz
  have h := hp.mul_isBigO (hd.isBigO_one ℝ)
  have h' := h.const_mul_left (A * B ^ (s + 1))
  convert h' using 1 <;> funext Y
  · simp only [mul_pow, pow_mul, pow_add, pow_one]
    ring
  · simp

#print axioms geometric_majorant_littleO
end QuantumNLS.TerraMultiRound57Tail

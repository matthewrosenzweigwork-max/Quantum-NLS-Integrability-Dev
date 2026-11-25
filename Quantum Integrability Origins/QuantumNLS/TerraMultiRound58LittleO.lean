import QuantumNLS.TerraMultiRound57CoefficientUniqueness

/-! Convert a quantitative inverse-power estimate to the fixed-field little-oh needed for uniqueness. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound58LittleO

/-- A one-power-better eventual error bound implies little-oh at order N. -/
theorem inverse_power_bound_littleO (N : ℕ) (f : ℝ → ℂ) (C : ℝ)
    (h : ∀ᶠ Y : ℝ in atTop, ‖f Y‖ ≤ C * (Y ^ (N + 1))⁻¹) :
    f =o[atTop] (fun Y : ℝ => Y⁻¹ ^ N) := by
  have hb : f =O[atTop] (fun Y : ℝ => C * (Y⁻¹ ^ (N + 1))) := by
    apply IsBigO.of_bound'
    filter_upwards [h] with Y hY
    have he : ‖f Y‖ ≤ C * Y⁻¹ ^ (N + 1) := by simpa [inv_pow] using hY
    exact he.trans (le_abs_self _)
  have hz : Tendsto (fun Y : ℝ => Y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hp : (fun Y : ℝ => Y⁻¹ ^ (N + 1)) =o[atTop] (fun Y : ℝ => Y⁻¹ ^ N) :=
    (isLittleO_pow_pow (𝕜 := ℝ) (by omega : N < N + 1)).comp_tendsto hz
  exact hb.trans_isLittleO (hp.const_mul_left C)

#print axioms inverse_power_bound_littleO
end QuantumNLS.TerraMultiRound58LittleO

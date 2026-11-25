import NlsGge.GK38.AbelianRealDiagonalOperator
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Normed.Group.Continuity

/-! Source finite-head/tail diagonal lower bound through the pinned cofinite API.
UNCOMPILED conditional coefficient preparation; concrete actual-Q premises remain
to be realized by the actual nonzero and row-error modules. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38.P3DiagonalOperator
noncomputable section

theorem exists_pos_lower_of_square_error (n : ℤ) (d a : P2Index38 n → ℝ)
    (hne : ∀ m, d m ≠ 0) (ha0 : ∀ m, 0 ≤ a m)
    (has : Summable (fun m => a m^2)) (herror : ∀ m, ‖d m-2‖ ≤ a m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m, δ ≤ ‖d m‖ := by
  have ha2 : Tendsto (fun m => a m^2) cofinite (𝓝 0) := has.tendsto_cofinite_zero
  have ha : Tendsto a cofinite (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp ha2
    have hsqrt : (fun m => Real.sqrt (a m^2)) = a := by
      funext m
      rw [Real.sqrt_sq_eq_abs,abs_of_nonneg (ha0 m)]
    change Tendsto (fun m => Real.sqrt (a m^2)) cofinite (𝓝 (Real.sqrt 0)) at hs
    simpa only [hsqrt,Real.sqrt_zero] using hs
  have hd0 : Tendsto (fun m => d m-2) cofinite (𝓝 0) := squeeze_zero_norm herror ha
  have hd : Tendsto d cofinite (𝓝 (2 : ℝ)) := by
    simpa only [sub_add_cancel,zero_add] using hd0.add_const 2
  have hinv := (hd.inv₀ (by norm_num : (2 : ℝ) ≠ 0)).norm
  obtain ⟨B,hB⟩ := hinv.bddAbove_range_of_cofinite
  let M : ℝ := max B 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right B 1)
  refine ⟨M⁻¹,inv_pos.mpr hM,?_⟩
  intro m
  have hb : ‖(d m)⁻¹‖ ≤ M := (hB (mem_range_self m)).trans (le_max_left B 1)
  have he : ‖d m‖*‖(d m)⁻¹‖ = 1 := by
    rw [← norm_mul,mul_inv_cancel₀ (hne m),norm_one]
  have hmul : 1 ≤ ‖d m‖*M := by
    rw [← he]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  rw [← one_div]
  exact (div_le_iff₀ hM).mpr hmul

end
end NlsGge.GK38.P3DiagonalOperator

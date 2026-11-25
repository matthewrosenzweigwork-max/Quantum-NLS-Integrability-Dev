import NlsGge.GK38.PeriodicLabellingDefs

/-! # S2: scalar radius monotonicity, isolated after the bounded API replan -/
set_option autoImplicit false
namespace NlsGge.GK38

theorem countingRadius_scalar_mono38 {x y : ℝ} (h : x ≤ y) :
    x * Real.pi + Real.pi / 4 ≤ y * Real.pi + Real.pi / 4 := by
  have hb : x * Real.pi ≤ y * Real.pi := mul_le_mul_of_nonneg_right h Real.pi_pos.le
  linarith

theorem countingRadius_mono38 : Monotone countingRadius38 := by
  intro N M h
  have hc : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
  exact countingRadius_scalar_mono38 hc

end NlsGge.GK38

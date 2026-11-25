import NlsGge.GK38.PeriodicLabellingCriticalFree

/-! # S2: independently checked nonzero sine witness after the bounded API replan -/
set_option autoImplicit false
namespace NlsGge.GK38

theorem free_sine_half_ne38 : Complex.sin ((Real.pi / 2 : ℝ) : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_sin, Real.sin_pi_div_two]
  norm_num

end NlsGge.GK38

import QuantumNLS.TerraMultiRound47ShiftedMode

/-! Exact L¹ majorant for damped Fourier modes. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound47ModeL1

/-- Translation of a mode is unimodular, so damping determines its norm. -/
theorem damped_mode_norm (Y p v : ℝ) (c : ℂ) :
    ‖(Real.exp (-v) : ℂ) * Complex.exp (Complex.I * (p : ℂ) * ((-v / Y : ℝ) : ℂ)) * c‖ =
      Real.exp (-v) * ‖c‖ := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The L¹ norm of the damped mode equals the magnitude of its coefficient. -/
theorem damped_mode_integral_norm (Y p : ℝ) (c : ℂ) :
    (∫ v : ℝ in Ioi 0,
      ‖(Real.exp (-v) : ℂ) * Complex.exp (Complex.I * (p : ℂ) * ((-v / Y : ℝ) : ℂ)) * c‖) = ‖c‖ := by
  simp_rw [damped_mode_norm]
  rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]

#print axioms damped_mode_norm
#print axioms damped_mode_integral_norm
end QuantumNLS.TerraMultiRound47ModeL1

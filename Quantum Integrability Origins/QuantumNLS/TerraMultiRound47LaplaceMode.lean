import QuantumNLS.TerraMultiRound38SignedResolvent
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The Laplace-shift formula on one Fourier mode. The operator-valued
Bochner identity and treewise Fubini are separate obligations. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound47LaplaceMode

/-- The exponentially damped shifted mode is integrable on the positive half-line. -/
theorem shifted_mode_integrable (Y p : ℝ) (c : ℂ) :
    IntegrableOn (fun v : ℝ => Complex.exp (((-1 : ℂ) - Complex.I * (p / Y : ℝ)) * v) * c)
      (Ioi 0) := by
  apply Integrable.mul_const
  apply integrableOn_exp_mul_complex_Ioi
  simp

/-- The modewise Laplace integral has the signed resolvent multiplier,
including the external factor `Y⁻¹`. -/
theorem shifted_mode_integral (Y p : ℝ) (hY : Y ≠ 0) (c : ℂ) :
    (Y⁻¹ : ℂ) * (∫ v : ℝ in Ioi 0,
      Complex.exp (((-1 : ℂ) - Complex.I * (p / Y : ℝ)) * v) * c) =
      c / ((Y : ℂ) + Complex.I * p) := by
  rw [integral_mul_const, integral_exp_mul_complex_Ioi (by simp :
    (((-1 : ℂ) - Complex.I * (p / Y : ℝ))).re < 0)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div]
  have hYc : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY
  have hd : (1 : ℂ) + Complex.I * (p / Y : ℝ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
  push_cast
  field_simp
  simp only [sub_eq_add_neg, ← neg_add, div_neg, neg_neg]

#print axioms shifted_mode_integrable
#print axioms shifted_mode_integral
end QuantumNLS.TerraMultiRound47LaplaceMode

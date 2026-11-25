import QuantumNLS.TerraMultiRound47LaplaceMode

/-! The Fourier-mode integral in the source's damped translation form. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound47ShiftedMode
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.TerraMultiRound38SignedResolvent
open QuantumNLS.TerraMultiRound47LaplaceMode

/-- Pointwise identification of the exponential damping and translation phase. -/
theorem damped_phase (Y p v : ℝ) (c : ℂ) :
    (Real.exp (-v) : ℂ) * Complex.exp (Complex.I * (p : ℂ) * ((-v / Y : ℝ) : ℂ)) * c =
      Complex.exp (((-1 : ℂ) - Complex.I * (p / Y : ℝ)) * v) * c := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Damped translations of each Fourier coefficient are integrable. -/
theorem damped_phase_integrable (Y p : ℝ) (c : ℂ) :
    IntegrableOn (fun v : ℝ => (Real.exp (-v) : ℂ) *
      Complex.exp (Complex.I * (p : ℂ) * ((-v / Y : ℝ) : ℂ)) * c) (Ioi 0) := by
  simpa only [damped_phase] using shifted_mode_integrable Y p c

/-- The signed resolvent Fourier coefficient equals the Laplace integral of
its damped translated mode, for either nonzero real spectral parameter. -/
theorem signed_resolvent_mode_shift (L Y : ℝ) (hY : Y ≠ 0) (c : ℤ → ℂ) (k : ℤ) :
    signedResolvent L Y c k = (Y⁻¹ : ℂ) * (∫ v : ℝ in Ioi 0,
      (Real.exp (-v) : ℂ) * Complex.exp
        (Complex.I * (freq L k : ℂ) * ((-v / Y : ℝ) : ℂ)) * c k) := by
  simp only [damped_phase, signedResolvent]
  exact (shifted_mode_integral Y (freq L k) hY (c k)).symm

#print axioms damped_phase
#print axioms damped_phase_integrable
#print axioms signed_resolvent_mode_shift
end QuantumNLS.TerraMultiRound47ShiftedMode

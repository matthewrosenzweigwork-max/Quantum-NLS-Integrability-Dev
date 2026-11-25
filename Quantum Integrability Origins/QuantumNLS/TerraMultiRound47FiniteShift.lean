import QuantumNLS.TerraMultiRound47ShiftedMode

/-! Laplace-shift representation for finite Fourier sums, pointwise in space. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
namespace QuantumNLS.TerraMultiRound47FiniteShift
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.TerraMultiRound38SignedResolvent
open QuantumNLS.TerraMultiRound47ShiftedMode QuantumNLS.TerraMultiRound47LaplaceMode

/-- A shifted spatial Fourier mode has the phase required by the modewise identity. -/
theorem shifted_spatial_mode (Y p x v : ℝ) (c : ℂ) :
    (Real.exp (-v) : ℂ) * (c * Complex.exp (Complex.I * (p : ℂ) * ((x - v / Y : ℝ) : ℂ))) =
    (Real.exp (-v) : ℂ) * Complex.exp (Complex.I * (p : ℂ) * ((-v / Y : ℝ) : ℂ)) *
      (c * Complex.exp (Complex.I * (p : ℂ) * x)) := by
  have h : Complex.I * (p : ℂ) * ((x - v / Y : ℝ) : ℂ) =
      Complex.I * (p : ℂ) * ((-v / Y : ℝ) : ℂ) + Complex.I * (p : ℂ) * x := by
    push_cast
    ring
  rw [h, Complex.exp_add]
  ring

/-- Exact source-form Laplace representation for every finite Fourier polynomial. -/
theorem finite_fourier_laplace (L Y x : ℝ) (hY : Y ≠ 0) (c : ℤ → ℂ) (s : Finset ℤ) :
    (∑ k ∈ s, signedResolvent L Y c k * Complex.exp (Complex.I * (freq L k : ℂ) * x)) =
    (Y⁻¹ : ℂ) * ∫ v : ℝ in Ioi 0, (Real.exp (-v) : ℂ) *
      (∑ k ∈ s, c k * Complex.exp (Complex.I * (freq L k : ℂ) * ((x - v / Y : ℝ) : ℂ))) := by
  have heq : ∀ v : ℝ, (Real.exp (-v) : ℂ) *
      (∑ k ∈ s, c k * Complex.exp (Complex.I * (freq L k : ℂ) * ((x - v / Y : ℝ) : ℂ))) =
      ∑ k ∈ s, (Real.exp (-v) : ℂ) * Complex.exp
        (Complex.I * (freq L k : ℂ) * ((-v / Y : ℝ) : ℂ)) *
          (c k * Complex.exp (Complex.I * (freq L k : ℂ) * x)) := by
    intro v
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact shifted_spatial_mode Y (freq L k) x v (c k)
  simp_rw [heq]
  rw [integral_finsetSum s (fun k _ => damped_phase_integrable Y (freq L k) _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h := shifted_mode_integral Y (freq L k) hY (c k * Complex.exp (Complex.I * (freq L k : ℂ) * x))
  simp_rw [damped_phase]
  rw [h]
  simp only [signedResolvent]
  ring

#print axioms shifted_spatial_mode
#print axioms finite_fourier_laplace
end QuantumNLS.TerraMultiRound47FiniteShift

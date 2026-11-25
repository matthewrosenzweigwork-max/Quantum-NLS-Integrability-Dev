import QuantumNLS.TerraMultiRound47FiniteShift
import QuantumNLS.TerraMultiRound47ModeL1

/-! Laplace-shift identity for absolutely summable Fourier series. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound47SeriesShift
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.TerraMultiRound38SignedResolvent
open QuantumNLS.TerraMultiRound47ShiftedMode QuantumNLS.TerraMultiRound47FiniteShift
open QuantumNLS.TerraMultiRound47ModeL1 QuantumNLS.TerraMultiRound47LaplaceMode

/-- Pointwise Laplace-shift identity for any absolutely summable Fourier
series. In particular this is applicable to the Fourier series of H¹ fields. -/
theorem summable_fourier_laplace (L Y x : ℝ) (hY : Y ≠ 0) (c : ℤ → ℂ)
    (hc : Summable fun k => ‖c k‖) :
    (∑' k, signedResolvent L Y c k * Complex.exp (Complex.I * (freq L k : ℂ) * x)) =
    (Y⁻¹ : ℂ) * ∫ v : ℝ in Ioi 0, (Real.exp (-v) : ℂ) *
      (∑' k, c k * Complex.exp (Complex.I * (freq L k : ℂ) * ((x - v / Y : ℝ) : ℂ))) := by
  let F : ℤ → ℝ → ℂ := fun k v => (Real.exp (-v) : ℂ) *
    Complex.exp (Complex.I * (freq L k : ℂ) * ((-v / Y : ℝ) : ℂ)) *
      (c k * Complex.exp (Complex.I * (freq L k : ℂ) * x))
  have hF : ∀ k, IntegrableOn (F k) (Ioi 0) := fun k => damped_phase_integrable Y (freq L k) _
  have hnorm : ∀ k, (∫ v : ℝ in Ioi 0, ‖F k v‖) = ‖c k‖ := by
    intro k
    rw [show (∫ v : ℝ in Ioi 0, ‖F k v‖) =
      ‖c k * Complex.exp (Complex.I * (freq L k : ℂ) * x)‖ from damped_mode_integral_norm Y _ _]
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hsum : Summable fun k => ∫ v : ℝ in Ioi 0, ‖F k v‖ := by
    simpa only [hnorm] using hc
  have hexchange := integral_tsum_of_summable_integral_norm hF hsum
  have heach : ∀ k, signedResolvent L Y c k * Complex.exp (Complex.I * (freq L k : ℂ) * x) =
      (Y⁻¹ : ℂ) * ∫ v : ℝ in Ioi 0, F k v := by
    intro k
    have h := shifted_mode_integral Y (freq L k) hY
      (c k * Complex.exp (Complex.I * (freq L k : ℂ) * x))
    have heq : (∫ v : ℝ in Ioi 0, F k v) = ∫ v : ℝ in Ioi 0,
      Complex.exp (((-1 : ℂ) - Complex.I * (freq L k / Y : ℝ)) * v) *
        (c k * Complex.exp (Complex.I * (freq L k : ℂ) * x)) := by
      apply integral_congr_ae
      filter_upwards with v
      exact damped_phase Y (freq L k) v _
    rw [heq, h]
    simp only [signedResolvent]
    ring
  have hpoint : ∀ v, (∑' k, F k v) = (Real.exp (-v) : ℂ) *
      (∑' k, c k * Complex.exp (Complex.I * (freq L k : ℂ) * ((x - v / Y : ℝ) : ℂ))) := by
    intro v
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    exact (shifted_spatial_mode Y (freq L k) x v (c k)).symm
  calc
    _ = ∑' k, (Y⁻¹ : ℂ) * ∫ v : ℝ in Ioi 0, F k v := tsum_congr heach
    _ = (Y⁻¹ : ℂ) * (∑' k, ∫ v : ℝ in Ioi 0, F k v) := by rw [tsum_mul_left]
    _ = (Y⁻¹ : ℂ) * ∫ v : ℝ in Ioi 0, ∑' k, F k v := by rw [hexchange]
    _ = _ := by simp_rw [hpoint]

#print axioms summable_fourier_laplace
end QuantumNLS.TerraMultiRound47SeriesShift

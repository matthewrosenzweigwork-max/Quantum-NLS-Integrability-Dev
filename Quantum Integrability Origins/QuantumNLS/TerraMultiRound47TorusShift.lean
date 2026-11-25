import QuantumNLS.TerraMultiRound47SeriesShift
import QuantumNLS.SobolevSpaces

/-! Laplace shifts in the normalized Fourier-series model on the torus. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set AddCircle
namespace QuantumNLS.TerraMultiRound47TorusShift
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.TerraMultiRound38SignedResolvent
open QuantumNLS.TerraMultiRound47SeriesShift QuantumNLS.Fourier QuantumNLS.Sobolev

/-- The workspace's orthonormal series in unnormalized exponential coordinates. -/
theorem normalized_series_real (L : ℝ) [Fact (0 < L)] (b : ℤ → ℂ) (t : ℝ) :
    seriesRep L b (t : AddCircle L) = ∑' k,
      (b k * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)) * Complex.exp (Complex.I * (RiccatiSobolevE1.freq L k : ℂ) * t) := by
  unfold seriesRep
  apply tsum_congr
  intro k
  rw [mode_coe]
  have he : (2 : ℂ) * Real.pi * Complex.I * (k : ℂ) * t / L =
      Complex.I * (RiccatiSobolevE1.freq L k : ℂ) * t := by
    unfold RiccatiSobolevE1.freq
    push_cast
    ring
  rw [he]
  ring

/-- The signed resolvent commutes with the constant Fourier normalization. -/
theorem normalized_signed_coeff (L Y : ℝ) (a : ℤ → ℂ) (k : ℤ) :
    signedResolvent L Y (fun n => a n * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)) k =
      signedResolvent L Y a k * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) := by
  simp only [signedResolvent]
  ring

/-- The Laplace-shift formula for the realized continuous torus Fourier series. -/
theorem torus_series_laplace (L : ℝ) [Fact (0 < L)] (Y : ℝ) (hY : Y ≠ 0)
    (a : ℤ → ℂ) (ha : Summable fun k => ‖a k‖) (x : ℝ) :
    seriesRep L (signedResolvent L Y a) (x : AddCircle L) =
      (Y⁻¹ : ℂ) * ∫ v : ℝ in Ioi 0, (Real.exp (-v) : ℂ) *
        seriesRep L a ((x - v / Y : ℝ) : AddCircle L) := by
  have hc : Summable fun k => ‖a k * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)‖ := by
    simpa only [norm_mul] using ha.mul_right ‖(((Real.sqrt L)⁻¹ : ℝ) : ℂ)‖
  have h := summable_fourier_laplace L Y x hY (fun k => a k * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)) hc
  simp_rw [normalized_signed_coeff] at h
  simp_rw [← normalized_series_real] at h
  exact h

#print axioms normalized_series_real
#print axioms normalized_signed_coeff
#print axioms torus_series_laplace
end QuantumNLS.TerraMultiRound47TorusShift

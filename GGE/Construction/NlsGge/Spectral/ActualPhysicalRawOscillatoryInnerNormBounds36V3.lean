import NlsGge.Spectral.ActualPhysicalRawOscillatoryInnerFourierIdentity36V1
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The actual decaying channel loses no constant when transferred to its
Fourier amplitude. The raw cover representative is handled only a.e. -/
theorem actualPhysicalRawOscillatoryInner00_norm_le_fourier36V3
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (x : ℝ) :
    ‖∫ r in (0 : ℝ)..(p.1 : ℝ),
      Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
        (((p.1 : ℝ) : ℂ)-(r : ℂ)))*star (naturalPhysicalCoverL2 u (r : SpectralCircle))‖ ≤
      ‖Real.Lp.fourierTransformCLM ℝ ℂ
        (actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀ p) (x/Real.pi)‖ := by
  rw [actualPhysicalRawOscillatoryInner00_fourierIdentity36V1 u Y₀ hY₀ p x, norm_mul]
  have hre : (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
      ((p.1 : ℝ) : ℂ)).re = -2*(p.2 : ℝ)*(p.1 : ℝ) := by
    simp [Complex.mul_re, Complex.mul_im]
    <;> ring
  have he : ‖Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
      ((p.1 : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, hre]
    exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg p.2.property.1 p.1.property.1])
  exact mul_le_of_le_one_left (norm_nonneg _) he

/-- The opposite channel has the actual bounded-height constant exp(2Y₀),
with the opposite frequency and unstarred raw source retained. -/
theorem actualPhysicalRawOscillatoryInner11_norm_le_fourier36V3
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (x : ℝ) :
    ‖∫ r in (0 : ℝ)..(p.1 : ℝ),
      Complex.exp (-2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
        (((p.1 : ℝ) : ℂ)-(r : ℂ)))*naturalPhysicalCoverL2 u (r : SpectralCircle)‖ ≤
      Real.exp (2*Y₀) * ‖Real.Lp.fourierTransformCLM ℝ ℂ
        (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀ p) (-x/Real.pi)‖ := by
  rw [actualPhysicalRawOscillatoryInner11_fourierIdentity36V1 u Y₀ hY₀ p x, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hre : (-2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
      ((p.1 : ℝ) : ℂ)).re = 2*(p.2 : ℝ)*(p.1 : ℝ) := by
    simp [Complex.mul_re, Complex.mul_im]
    <;> ring
  rw [Complex.norm_exp, hre]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left p.1.property.2 p.2.property.1, p.2.property.2]
end NlsGge.SpectralFoundations
end

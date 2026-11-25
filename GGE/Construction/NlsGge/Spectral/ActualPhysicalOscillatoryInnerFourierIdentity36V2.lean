import NlsGge.Spectral.ActualPhysicalHeightAmplitudeFourierRepresentation35V2
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Exact Fourier representation of the physical decaying inner source
integral, with the library's negative two-pi Fourier convention. It supplies
no compactness or high-energy decay hypothesis. -/
theorem actualPhysicalOscillatoryInner00_fourierIdentity36V2
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (x : ℝ) :
    (∫ r in (0 : ℝ)..(p.1 : ℝ),
      Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
        (((p.1 : ℝ) : ℂ)-(r : ℂ)))*star (actualPhysicalL2SourcePotential u r)) =
      Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
        ((p.1 : ℝ) : ℂ)) *
      Real.Lp.fourierTransformCLM ℝ ℂ
        (actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀ p) (x/Real.pi) := by
  rw [actualPhysicalHeightAmplitude00Lp1_fourierRepresentation35,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  have he : 2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
      (((p.1 : ℝ) : ℂ)-(r : ℂ)) =
      2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*((p.1 : ℝ) : ℂ)+
      (((-2*Real.pi*r*(x/Real.pi) : ℝ) : ℂ)*Complex.I)+
      ((2*(p.2 : ℝ)*r : ℝ) : ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [he, Complex.exp_add, Complex.exp_add]
  ring

/-- The opposite physical channel has the opposite Fourier frequency and
the negative height weight; both signs are retained exactly. -/
theorem actualPhysicalOscillatoryInner11_fourierIdentity36V2
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (x : ℝ) :
    (∫ r in (0 : ℝ)..(p.1 : ℝ),
      Complex.exp (-2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
        (((p.1 : ℝ) : ℂ)-(r : ℂ)))*actualPhysicalL2SourcePotential u r) =
      Complex.exp (-2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
        ((p.1 : ℝ) : ℂ)) *
      Real.Lp.fourierTransformCLM ℝ ℂ
        (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀ p) (-x/Real.pi) := by
  rw [actualPhysicalHeightAmplitude11Lp1_fourierRepresentation35,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  have he : -2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
      (((p.1 : ℝ) : ℂ)-(r : ℂ)) =
      -2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*((p.1 : ℝ) : ℂ)+
      (((-2*Real.pi*r*(-x/Real.pi) : ℝ) : ℂ)*Complex.I)+
      ((-2*(p.2 : ℝ)*r : ℝ) : ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [he, Complex.exp_add, Complex.exp_add]
  ring

end NlsGge.SpectralFoundations
end

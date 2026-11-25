import NlsGge.Spectral.ActualPhysicalOscillatoryInnerFourierIdentity36V2
import NlsGge.Spectral.ActualPhysicalUnitRawCoverNorm32V1
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Null-set-safe transfer of the exact physical inner Fourier identity to
 the actual raw cover representative used by the Dyson coefficient. -/
theorem actualPhysicalRawOscillatoryInner00_fourierIdentity36V1
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (x : ℝ) :
    (∫ r in (0 : ℝ)..(p.1 : ℝ),
      Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
        (((p.1 : ℝ) : ℂ)-(r : ℂ)))*star (naturalPhysicalCoverL2 u (r : SpectralCircle))) =
      Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
        ((p.1 : ℝ) : ℂ)) *
      Real.Lp.fourierTransformCLM ℝ ℂ
        (actualPhysicalHeightAmplitude00Lp1_35V2 u Y₀ hY₀ p) (x/Real.pi) := by
  have hAE : ∀ᵐ r ∂volume, r ∈ Set.Ioc (0 : ℝ) 1 →
      actualPhysicalL2SourcePotential u r = naturalPhysicalCoverL2 u (r : SpectralCircle) :=
    (ae_restrict_iff' measurableSet_Ioc).1 (actualPhysicalSourcePotential_rawCover_ae32 u)
  calc
    _ = ∫ r in (0 : ℝ)..(p.1 : ℝ),
      Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
        (((p.1 : ℝ) : ℂ)-(r : ℂ)))*star (actualPhysicalL2SourcePotential u r) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hAE] with r hr
      intro hrs
      have hs : r ∈ Set.Ioc (0 : ℝ) (p.1 : ℝ) := by
        simpa only [Set.uIoc_of_le p.1.property.1] using hrs
      rw [hr ⟨hs.1, hs.2.trans p.1.property.2⟩]
    _ = _ := actualPhysicalOscillatoryInner00_fourierIdentity36V2 u Y₀ hY₀ p x

/-- Opposite-channel null-set-safe transfer, preserving the negative height
weight and opposite Fourier frequency. No pointwise representative equality
or unproved decay is used. -/
theorem actualPhysicalRawOscillatoryInner11_fourierIdentity36V1
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (x : ℝ) :
    (∫ r in (0 : ℝ)..(p.1 : ℝ),
      Complex.exp (-2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
        (((p.1 : ℝ) : ℂ)-(r : ℂ)))*naturalPhysicalCoverL2 u (r : SpectralCircle)) =
      Complex.exp (-2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
        ((p.1 : ℝ) : ℂ)) *
      Real.Lp.fourierTransformCLM ℝ ℂ
        (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀ p) (-x/Real.pi) := by
  have hAE : ∀ᵐ r ∂volume, r ∈ Set.Ioc (0 : ℝ) 1 →
      actualPhysicalL2SourcePotential u r = naturalPhysicalCoverL2 u (r : SpectralCircle) :=
    (ae_restrict_iff' measurableSet_Ioc).1 (actualPhysicalSourcePotential_rawCover_ae32 u)
  calc
    _ = ∫ r in (0 : ℝ)..(p.1 : ℝ),
      Complex.exp (-2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
        (((p.1 : ℝ) : ℂ)-(r : ℂ)))*actualPhysicalL2SourcePotential u r := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hAE] with r hr
      intro hrs
      have hs : r ∈ Set.Ioc (0 : ℝ) (p.1 : ℝ) := by
        simpa only [Set.uIoc_of_le p.1.property.1] using hrs
      rw [hr ⟨hs.1, hs.2.trans p.1.property.2⟩]
    _ = _ := actualPhysicalOscillatoryInner11_fourierIdentity36V2 u Y₀ hY₀ p x
end NlsGge.SpectralFoundations
end

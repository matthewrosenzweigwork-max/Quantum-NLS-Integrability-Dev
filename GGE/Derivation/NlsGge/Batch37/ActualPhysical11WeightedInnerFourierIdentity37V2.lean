import NlsGge.Spectral.ActualPhysicalHeightAmplitudeFourierRepresentation35V2
import NlsGge.Spectral.ActualPhysicalHeightAmplitudeJointParameterBound36V6
import NlsGge.Spectral.ActualPhysicalUnitRawCoverNorm32V1
import NlsGge.Spectral.ComplexRealOscillatoryPhase35V1
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
/-- Direct weighted actual raw-cover 11 inner Fourier identity; no growing
exponential is introduced, and rough representatives are transferred only AE.
Outer pair integration and decay are separate obligations. -/
theorem actualPhysical11WeightedInner_fourierIdentity37V2
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (x : ℝ) :
    (∫ r in (0 : ℝ)..(p.1 : ℝ),
      naturalPhysicalCoverL2 u (r : SpectralCircle) *
        (complexRealOscillatoryPhase35 (2*x) r *
          (Real.exp (-2*(p.2 : ℝ)*r) : ℂ))) =
      Real.Lp.fourierTransformCLM ℝ ℂ
        (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ p) (-x/Real.pi) := by
  have hAE : ∀ᵐ r ∂volume, r ∈ Set.Ioc (0 : ℝ) 1 →
      actualPhysicalL2SourcePotential u r = naturalPhysicalCoverL2 u (r : SpectralCircle) :=
    (ae_restrict_iff' measurableSet_Ioc).1 (actualPhysicalSourcePotential_rawCover_ae32 u)
  change _ = Real.Lp.fourierTransformCLM ℝ ℂ
    (actualPhysicalHeightAmplitude11Lp1_35V2 u Y₀ hY₀ p) (-x/Real.pi)
  rw [actualPhysicalHeightAmplitude11Lp1_fourierRepresentation35]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hAE] with r hr
  intro hrs
  have hs : r ∈ Set.Ioc (0 : ℝ) (p.1 : ℝ) := by
    simpa only [Set.uIoc_of_le p.1.property.1] using hrs
  rw [hr ⟨hs.1, hs.2.trans p.1.property.2⟩]
  have hphase : (((-2*Real.pi*r*(-x/Real.pi) : ℝ) : ℂ)*Complex.I) =
      Complex.I*((2*x : ℝ) : ℂ)*(r : ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [hphase, ← Complex.ofReal_exp]
  dsimp only [complexRealOscillatoryPhase35]
  ring
end NlsGge.SpectralFoundations
end

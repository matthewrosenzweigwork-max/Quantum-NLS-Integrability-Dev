import NlsGge.Schur.CoveredH1SpectralMultiplier

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- Pointwise Fourier-integrand identity for the actual H¹ multiplier applied
to a character. This isolates the representative-level scalar calculation
before the coefficient integral is rewritten. -/
theorem coveredH1SpectralMultiplier_character_integrand_ae
    (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (m l : ℤ) :
    (fun x : SpectralCircle =>
      inner ℂ (spectralBasis m x)
        (coveredH1SpectralMultiplier u hu (spectralBasis (-l)) x)) =ᵐ[spectralHaar]
      fun x => fourier (-(m + l)) x * naturalPhysicalCoverH1Bounded u hu x := by
  filter_upwards [coeFn_fourierLp (T := (2 : ℝ)) 2 m,
    coveredH1SpectralMultiplier_ae u hu (spectralBasis (-l)),
    coeFn_fourierLp (T := (2 : ℝ)) 2 (-l)] with x hm hmul hl
  change fourierLp (T := (2 : ℝ)) (2 : ℝ≥0∞) m x = _ at hm
  change fourierLp (T := (2 : ℝ)) (2 : ℝ≥0∞) (-l) x = _ at hl
  change coveredH1SpectralMultiplier u hu (spectralBasis (-l)) x =
    naturalPhysicalCoverH1Bounded u hu x *
      fourierLp (T := (2 : ℝ)) (2 : ℝ≥0∞) (-l) x at hmul
  change inner ℂ (fourierLp (T := (2 : ℝ)) (2 : ℝ≥0∞) m x)
      (coveredH1SpectralMultiplier u hu (spectralBasis (-l)) x) = _
  rw [hm, hmul, hl, RCLike.inner_apply', ← fourier_neg]
  calc
    (fourier (-m) x) *
        (naturalPhysicalCoverH1Bounded u hu x * (fourier (-l)) x) =
      ((fourier (-m) x) * (fourier (-l)) x) *
        naturalPhysicalCoverH1Bounded u hu x := by ring
    _ = fourier (-m + -l) x * naturalPhysicalCoverH1Bounded u hu x := by
      rw [← fourier_add]
    _ = fourier (-(m + l)) x * naturalPhysicalCoverH1Bounded u hu x := by
      congr 1
      ring

end NlsGge.Schur

import NlsGge.Analysis.H1Multiplication
import NlsGge.Analysis.NaturalCoverCoefficients

/-! Actual bounded class of a varying H1 field on the doubled circle.
This is a field primitive; multiplication and paired potential remain separate. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Analysis
open NlsGge.Pilot NlsGge.Schur

def naturalPhysicalCoverH1Bounded (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) : Lp ℂ ∞ spectralHaar :=
  Lp.compMeasurePreserving naturalPhysicalCover naturalPhysicalCover_preserving
    (physicalH1Bounded u hu)

theorem naturalPhysicalCoverH1Bounded_ae (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    (naturalPhysicalCoverH1Bounded u hu : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      fun x => u (naturalPhysicalCover x) := by
  exact (Lp.coeFn_compMeasurePreserving (physicalH1Bounded u hu)
    naturalPhysicalCover_preserving).trans
    (naturalPhysicalCover_preserving.quasiMeasurePreserving.ae_eq_comp
      (physicalH1Bounded_coe_ae u hu))

theorem naturalPhysicalCoverH1Bounded_norm (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖naturalPhysicalCoverH1Bounded u hu‖ = ‖physicalH1Bounded u hu‖ :=
  Lp.norm_compMeasurePreserving (physicalH1Bounded u hu) naturalPhysicalCover_preserving

theorem naturalPhysicalCoverH1Bounded_norm_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ‖naturalPhysicalCoverH1Bounded u hu‖ ≤
      physicalH1MultiplierConstant * ‖physicalSobolevL2 1 u hu‖ := by
  rw [naturalPhysicalCoverH1Bounded_norm]
  apply ((physicalH1Bounded_norm_le u hu).trans
    (physicalH1Continuous_norm_bound u hu)).trans
  unfold physicalH1MultiplierConstant
  nlinarith [norm_nonneg (physicalSobolevL2 1 u hu)]

theorem naturalPhysicalCoverH1Bounded_halfShift (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Lp.compMeasurePreserving
      (fun x : SpectralCircle => x + ((1 : ℝ) : SpectralCircle)) halfShift_preserving
      (naturalPhysicalCoverH1Bounded u hu) = naturalPhysicalCoverH1Bounded u hu := by
  apply Lp.ext
  have hs := halfShift_preserving.quasiMeasurePreserving.ae_eq_comp
    (naturalPhysicalCoverH1Bounded_ae u hu)
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (naturalPhysicalCoverH1Bounded u hu) halfShift_preserving, hs,
    naturalPhysicalCoverH1Bounded_ae u hu] with x hout hs hfield
  change naturalPhysicalCoverH1Bounded u hu (x + ((1 : ℝ) : SpectralCircle)) =
    u (naturalPhysicalCover (x + ((1 : ℝ) : SpectralCircle))) at hs
  rw [hout]
  simp only [Function.comp_apply]
  rw [hs, naturalPhysicalCover_halfShift, hfield]

end NlsGge.Analysis

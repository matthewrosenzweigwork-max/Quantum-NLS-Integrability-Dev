import NlsGge.Hierarchy.RiccatiPhysicalH1CarrierAfterUnweightedCoordinateSecond
import NlsGge.Analysis.H1Fourier
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

/-! Isolated linearity prerequisites for the canonical H¹ representative.
These facts are separated from the full operator construction so their actual
continuous-map scalar/module elaboration can be checked independently. -/

namespace NlsGge.Pilot

open NlsGge.Analysis

private theorem carrierFourier_add (x y : SobolevHilbert 1) (n : ℤ) :
    physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate (x + y)) n =
      physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate x) n +
        physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate y) n := by
  rw [physicalH1CarrierToL2AfterAcceptedCoordinate_fourier,
    physicalH1CarrierToL2AfterAcceptedCoordinate_fourier,
    physicalH1CarrierToL2AfterAcceptedCoordinate_fourier]
  rfl

private theorem carrierFourier_smul (r : ℝ) (x : SobolevHilbert 1) (n : ℤ) :
    physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate (r • x)) n =
      (r : ℂ) * physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate x) n := by
  rw [physicalH1CarrierToL2AfterAcceptedCoordinate_fourier,
    physicalH1CarrierToL2AfterAcceptedCoordinate_fourier]
  rfl

private theorem real_complex_smul_fourierTerm
    (r : ℝ) (a : ℂ) (f : C(PhysicalCircle, ℂ)) :
    ((r : ℂ) * a) • f = r • (a • f) := by
  ext x
  change ((r : ℂ) * a) * f x = (r : ℂ) * (a * f x)
  ring

theorem physicalH1CarrierContinuousAfterAcceptedCoordinate_add
    (x y : SobolevHilbert 1) :
    physicalH1CarrierContinuousAfterAcceptedCoordinate (x + y) =
      physicalH1CarrierContinuousAfterAcceptedCoordinate x +
        physicalH1CarrierContinuousAfterAcceptedCoordinate y := by
  unfold physicalH1CarrierContinuousAfterAcceptedCoordinate physicalH1Continuous
  have hx := physicalH1_continuous_fourier_summable
    (physicalH1CarrierToL2AfterAcceptedCoordinate x)
    (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)
  have hy := physicalH1_continuous_fourier_summable
    (physicalH1CarrierToL2AfterAcceptedCoordinate y)
    (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable y)
  rw [← hx.tsum_add hy]
  apply tsum_congr
  intro n
  rw [carrierFourier_add]
  exact add_smul
    (physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate x) n)
    (physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate y) n)
    (fourier (T := (1 : ℝ)) n)

theorem physicalH1CarrierContinuousAfterAcceptedCoordinate_smul
    (r : ℝ) (x : SobolevHilbert 1) :
    physicalH1CarrierContinuousAfterAcceptedCoordinate (r • x) =
      r • physicalH1CarrierContinuousAfterAcceptedCoordinate x := by
  unfold physicalH1CarrierContinuousAfterAcceptedCoordinate physicalH1Continuous
  have hx := physicalH1_continuous_fourier_summable
    (physicalH1CarrierToL2AfterAcceptedCoordinate x)
    (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x)
  rw [← hx.tsum_const_smul r]
  apply tsum_congr
  intro n
  rw [carrierFourier_smul]
  exact real_complex_smul_fourierTerm r
    (physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate x) n)
    (fourier (T := (1 : ℝ)) n)

end NlsGge.Pilot

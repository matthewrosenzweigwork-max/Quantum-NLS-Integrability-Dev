import NlsGge.Hierarchy.RiccatiPhysicalH1CarrierAfterUnweightedCoordinateSecond
import NlsGge.Hierarchy.RiccatiPhysicalFourierL2RealLinearityPrerequisite
import NlsGge.Analysis.H1Fourier
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.Pilot

open NlsGge.Analysis

private theorem physicalH1Carrier_fourier_add_actual
    (x y : SobolevHilbert 1) (n : ℤ) :
    physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate (x + y)) n =
      physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate x) n +
        physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate y) n := by
  rw [physicalH1CarrierToL2AfterAcceptedCoordinate_fourier,
    physicalH1CarrierToL2AfterAcceptedCoordinate_fourier,
    physicalH1CarrierToL2AfterAcceptedCoordinate_fourier]
  rfl

private theorem physicalH1Carrier_fourier_smul_actual
    (r : ℝ) (x : SobolevHilbert 1) (n : ℤ) :
    physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate (r • x)) n =
      (r : ℂ) * physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate x) n := by
  rw [physicalH1CarrierToL2AfterAcceptedCoordinate_fourier,
    physicalH1CarrierToL2AfterAcceptedCoordinate_fourier]
  rfl

theorem physicalH1DerivativeClass_add_actual (x y : SobolevHilbert 1) :
    physicalH1FourierDerivativeClass
        (physicalH1CarrierToL2AfterAcceptedCoordinate (x + y))
        (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable (x + y)) =
      physicalH1FourierDerivativeClass
          (physicalH1CarrierToL2AfterAcceptedCoordinate x)
          (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x) +
        physicalH1FourierDerivativeClass
          (physicalH1CarrierToL2AfterAcceptedCoordinate y)
          (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable y) := by
  apply physicalFourierL2.injective
  conv_rhs => rw [map_add]
  apply lp.ext
  funext n
  simp only [physicalFourierL2_apply,
    physicalH1FourierDerivativeClass_fourier,
    physicalH1Carrier_fourier_add_actual,
    lp.coeFn_add, Pi.add_apply]
  ring

theorem physicalH1DerivativeClass_smul_actual (r : ℝ) (x : SobolevHilbert 1) :
    physicalH1FourierDerivativeClass
        (physicalH1CarrierToL2AfterAcceptedCoordinate (r • x))
        (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable (r • x)) =
      r • physicalH1FourierDerivativeClass
        (physicalH1CarrierToL2AfterAcceptedCoordinate x)
        (physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable x) := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_map_real_smul_actual_apply]
  simp only [physicalFourierL2_apply,
    physicalH1FourierDerivativeClass_fourier,
    physicalH1Carrier_fourier_smul_actual]
  ring

end NlsGge.Pilot

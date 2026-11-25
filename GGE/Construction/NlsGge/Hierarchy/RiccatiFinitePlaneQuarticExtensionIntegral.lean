import NlsGge.Hierarchy.RiccatiPhysicalH1FiniteProjectionRepresentatives
import NlsGge.Hierarchy.RiccatiPhysicalH1Q2ContinuousEnergyExtensionAfterScalarL1Prerequisites

set_option autoImplicit false

namespace NlsGge.Pilot

open MeasureTheory

/-- The quartic term in the actual H¹ Q₂ energy extension, on a finite
projection, is the physical quartic integral of its plane representative. -/
theorem physicalH1QuarticIntegral_finiteProjection_eq_plane
    (N : ℕ) (x : SobolevHilbert 1) :
    physicalH1QuarticIntegralAfterScalarL1Prerequisites
        (physicalH1CanonicalContinuousRepresentativeCLM
          (physicalH1FiniteProjection N x)) =
      ∫ y : PhysicalCircle,
        ‖planeField N (physicalH1FiniteProjectionPlane N x) y‖ ^ 4
          ∂spatialMeasure := by
  rw [physicalH1QuarticIntegralAfterScalarL1Prerequisites_eq_integral,
    physicalH1CanonicalContinuousRepresentative_finiteProjection_eq_plane]
  rfl

end NlsGge.Pilot

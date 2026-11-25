import NlsGge.Hierarchy.RiccatiPhysicalH1WeightedDerivativeSquareAfterRawHolderInnerPrerequisitesSecond
import NlsGge.Hierarchy.RiccatiPhysicalH1Q4CrossPairingAfterHolderInnerPrerequisitesThird
import NlsGge.Hierarchy.RiccatiPhysicalH1SixthPowerIntegralContinuityAfterCanonicalRepresentative
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot

/-- The actual continuous H¹ lower-order Q₄ candidate, assembled from the
cross-pairing, derivative-square, and sixth-power components. The H² leading
term is deliberately outside this functional. -/
def physicalH1Q4LowerOrderRemainderAfterCanonicalComponents
    (x : SobolevHilbert 1) : ℝ :=
  physicalH1Q4CrossPairingAfterCanonicalMultiplication x +
    8 * physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites x +
    2 * physicalH1SixthPowerIntegralAfterCanonicalRepresentative x

theorem continuous_physicalH1Q4LowerOrderRemainderAfterCanonicalComponents :
    Continuous physicalH1Q4LowerOrderRemainderAfterCanonicalComponents := by
  unfold physicalH1Q4LowerOrderRemainderAfterCanonicalComponents
  exact (continuous_physicalH1Q4CrossPairingAfterCanonicalMultiplication.add
    (continuous_const.mul
      continuous_physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites)).add
        (continuous_const.mul
          continuous_physicalH1SixthPowerIntegralAfterCanonicalRepresentative)

end NlsGge.Pilot

end

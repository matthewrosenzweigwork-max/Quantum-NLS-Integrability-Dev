import NlsGge.Schur.ActualComplementaryQVDJointInverseAndEqualDiagonalV5_30
import NlsGge.Schur.ActualSchurEffectiveJointAnalyticAfterDextV3_30

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- Exact definitional bridge from the named actual joint QVD parameter to its
concrete complementary-projection, potential, and center-extension factors. -/
theorem actualSchurQVDParameterLocalFactorizationMinimumV1_33
    (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) (z : ℂ) :
    actualComplementaryQVDJointParameterV5_30 n (z, p) =
      (freeResolventComplementaryProjectionTransported n).comp
        ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
          (actualFreeResolventCenterExtensionV1_30 n z)) := by
  rfl

end NlsGge.Schur

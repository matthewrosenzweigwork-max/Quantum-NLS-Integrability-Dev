import NlsGge.Schur.RootActualSchurQVDInverseHasFDerivAtActualParentMinimum36V4
set_option autoImplicit false
noncomputable section
namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot
/-- Exact named actual inverse-derivative value, without a derivative rule
or local typeclass transport. This isolates the span-value identity. -/
theorem rootActualSchurInverseDerivativeSpanIdentity36MinimumV1
    (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) (z : ℂ) :
    rootActualSchurQVDInverseDerivativeCLMMinimum36V4 n p z =
      ContinuousLinearMap.toSpanSingleton ℂ
        (-((actualComplementaryQVDJointInverseV5_30 n (z,p)).comp
          (((freeResolventComplementaryProjectionTransported n).comp
            ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
              ((actualFreeResolventCenterExtensionV1_30 n z).comp
                (actualFreeResolventCenterExtensionV1_30 n z)))).comp
                  (actualComplementaryQVDJointInverseV5_30 n (z,p))))) := by
  rfl
end NlsGge.Schur
end

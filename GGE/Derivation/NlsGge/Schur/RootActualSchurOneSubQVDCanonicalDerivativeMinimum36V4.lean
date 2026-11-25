import NlsGge.Schur.RootSchurDerivativeParentDataCoherenceMinimum36V1
import NlsGge.Schur.ActualSchurQVDCompositionDerivativeMinimumV5_33
import Mathlib.Analysis.Calculus.FDeriv.Add
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace NlsGge.Schur
local instance rootCanonicalEpGroup36V4 (n : ℤ) :
    NormedAddCommGroup (ParityPair n →L[ℂ] ParityPair n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance rootCanonicalEpSpace36V4 (n : ℤ) :
    NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
  ContinuousLinearMap.toNormedSpace
/-- Isolated derivative of the actual one-minus-QVD map in its canonical
CLM parents, with the two D factors exposed. No inverse or parent conversion
is postulated here. -/
theorem rootActualSchurOneSubQVD_hasFDerivAt_canonicalMinimum36V4
    (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30)
    (z : ℂ) (hz : z ∈ Metric.ball (spectralCenter n) 2) :
    HasFDerivAt
      (fun w : ℂ => 1 - (freeResolventComplementaryProjectionTransported n).comp
        ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
          (actualFreeResolventCenterExtensionV1_30 n w)))
      (ContinuousLinearMap.toSpanSingleton ℂ
        (-((freeResolventComplementaryProjectionTransported n).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
            (-(actualFreeResolventCenterExtensionV1_30 n z).comp
              (actualFreeResolventCenterExtensionV1_30 n z)))))) z := by
  have hT := actualComplementaryQVDParameter_hasFDerivAt_minimumV5_33 n p z hz
  have hneg (a : ParityPair n →L[ℂ] ParityPair n) :
      -ContinuousLinearMap.toSpanSingleton ℂ a =
        ContinuousLinearMap.toSpanSingleton ℂ (-a) := by
    apply ContinuousLinearMap.ext
    intro δ
    apply ContinuousLinearMap.ext
    intro x
    change -(δ • a x) = δ • -(a x)
    exact (smul_neg δ (a x)).symm
  simpa only [sub_eq_add_neg, Pi.neg_apply, hneg] using hT.neg.const_add (1 : ParityPair n →L[ℂ] ParityPair n)
end NlsGge.Schur
end

import NlsGge.Schur.ActualSchurEffectiveJointAnalyticAfterDextV3_30
import NlsGge.Schur.ActualSchurGreenProductBoundV3_31
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- The concrete linear sandwich map on the actual signed parity-pair
endomorphisms. It is expressed as composition of the checked bilinear CLM
`compL`, with explicit normed parents on the endomorphism carrier. -/
def actualSchurGreenSandwichCLMMinimumV3_32 (n : ℤ)
    (p : ActualSchurEffectiveH1PairV3_30) :
    (ParityPair n →L[ℂ] ParityPair n) →L[ℂ]
      (ParityPair n →L[ℂ] ParityPair n) := by
  let H : Type := ParityPair n
  let E : Type := H →L[ℂ] H
  letI : NormedRing E := ContinuousLinearMap.toNormedRing
  letI : NonUnitalNormedRing E := NormedRing.toNonUnitalNormedRing
  letI : NormedAddCommGroup E := NonUnitalNormedRing.toNormedAddCommGroup
  letI : NormedAlgebra ℂ E := ContinuousLinearMap.toNormedAlgebra
  letI : NormedSpace ℂ E := ContinuousLinearMap.toNormedSpace
  let P : H →L[ℂ] H := resonantParityPair n
  let V : H →L[ℂ] H :=
    actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p
  exact (ContinuousLinearMap.compL ℂ H H H (P.comp V)).comp
    ((ContinuousLinearMap.compL ℂ H H H).flip (V.comp P))

/-- Pointwise formula for the concrete map: `X ↦ P V X V P`. -/
theorem actualSchurGreenSandwichCLMMinimumV3_32_apply
    (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30)
    (X : ParityPair n →L[ℂ] ParityPair n) :
    actualSchurGreenSandwichCLMMinimumV3_32 n p X =
      (resonantParityPair n).comp
        ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
          (X.comp
            ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
              (resonantParityPair n)))) := by
  ext x
  rfl

end NlsGge.Schur

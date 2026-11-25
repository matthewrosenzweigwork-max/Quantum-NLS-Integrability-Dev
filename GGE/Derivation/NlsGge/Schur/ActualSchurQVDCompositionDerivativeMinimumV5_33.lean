import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30
import NlsGge.Schur.ActualComplementaryQVDJointInverseAndEqualDiagonalV5_30
import NlsGge.Schur.ActualSchurEffectiveJointAnalyticAfterDextV3_30
import NlsGge.Schur.ActualSchurConjugatedDextDerivativeMinimumV4_33
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
noncomputable section
open scoped Topology RightActions

namespace NlsGge.Schur

/-- The actual fixed-factor map `X ↦ Q V X` carries the proved Dext
span-singleton derivative to the corresponding concrete QVD derivative.
This is the linear-composition prerequisite for differentiating the actual
complementary QVD inverse. -/
theorem actualComplementaryQVDParameter_hasFDerivAt_minimumV5_33
    (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30)
    (z : ℂ) (hz : z ∈ Metric.ball (spectralCenter n) 2) :
    HasFDerivAt
      (fun w : ℂ =>
        (freeResolventComplementaryProjectionTransported n).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
            (actualFreeResolventCenterExtensionV1_30 n w)))
      (ContinuousLinearMap.toSpanSingleton ℂ
        ((freeResolventComplementaryProjectionTransported n).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
            (-(actualFreeResolventCenterExtensionV1_30 n z).comp
              (actualFreeResolventCenterExtensionV1_30 n z))))) z := by
  let Ep : Type := ParityPair n →L[ℂ] ParityPair n
  letI : NormedRing Ep := ContinuousLinearMap.toNormedRing
  letI : NonUnitalNormedRing Ep := NormedRing.toNonUnitalNormedRing
  letI : NormedAddCommGroup Ep := NonUnitalNormedRing.toNormedAddCommGroup
  letI : NormedAlgebra ℂ Ep := ContinuousLinearMap.toNormedAlgebra
  letI : NormedSpace ℂ Ep := ContinuousLinearMap.toNormedSpace
  let D : ℂ → Ep := actualFreeResolventCenterExtensionV1_30 n
  let Q : Ep := freeResolventComplementaryProjectionTransported n
  let V : Ep := actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p
  let LV : Ep →L[ℂ] Ep :=
    ContinuousLinearMap.compL ℂ (ParityPair n) (ParityPair n) (ParityPair n) V
  let LQ : Ep →L[ℂ] Ep :=
    ContinuousLinearMap.compL ℂ (ParityPair n) (ParityPair n) (ParityPair n) Q
  let L : Ep →L[ℂ] Ep := LQ.comp LV

  have hD := actualFreeResolventCenterExtension_hasFDerivAt_negativeSquareMinimumV4_33
    n z hz
  have hfunction :
      (fun w : ℂ => Q.comp (V.comp (D w))) =
        (fun w : ℂ => L (D w)) := by
    funext w
    dsimp [L, LQ, LV, ContinuousLinearMap.compL_apply]
    rfl
  have hmap :
      L.comp (ContinuousLinearMap.toSpanSingleton ℂ (-(D z).comp (D z))) =
        ContinuousLinearMap.toSpanSingleton ℂ (L (-(D z).comp (D z))) := by
    apply ContinuousLinearMap.ext
    intro δ
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.map_smul]
  have hraw : HasFDerivAt (fun w : ℂ => L (D w))
      (ContinuousLinearMap.toSpanSingleton ℂ (L (-(D z).comp (D z)))) z := by
    have hcomp := (L.hasFDerivAt).comp z hD
    exact hcomp.congr_fderiv hmap
  rw [← hfunction] at hraw
  exact hraw

end NlsGge.Schur

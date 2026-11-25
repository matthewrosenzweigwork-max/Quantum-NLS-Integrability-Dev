import NlsGge.Schur.ComplexCanonicalSelfModuleAgreement36MinimumV1
import NlsGge.Schur.ActualSchurEffectiveDerivativeSupportV1_32
import NlsGge.Schur.ActualSchurConjugatedDextDerivativeMinimumV4_33
import NlsGge.Schur.ActualSchurQVDCompositionDerivativeMinimumV5_33
import NlsGge.Schur.ActualSchurResolventDerivativeCancellationIdentityV3_33
import NlsGge.Schur.ActualSchurQVDParameterLocalFactorizationMinimumV1_33
import NlsGge.Schur.RootActualSchurQVDInverseHasFDerivAtActualParentMinimum36V4
import NlsGge.Schur.RootActualSchurInverseDerivativeSpanIdentity36MinimumV1
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
noncomputable section
open scoped Topology RightActions

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual source-order complementary resolvent `R = D S` has derivative
minus its square on the original signed spectral disk and independent complex
H¹ balls. This candidate consumes the separately gated actual two-D inverse
derivative theorem, applies the CLM product rule, and then uses the checked
actual cancellation identity. -/
theorem rootActualSchurResolventFamilyAfterDext_hasFDerivAt_negativeSquareMinimum36V8
    (radius : ℝ) (hradius : 1 ≤ radius)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * radius ^ 2 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hp₁ : ‖p.1‖ ≤ radius) (hp₂ : ‖p.2‖ ≤ radius) :
    HasFDerivAt
      (actualSchurResolventFamilyAfterDextV3_32 n p)
      (ContinuousLinearMap.toSpanSingleton ℂ
        (-((actualSchurResolventFamilyAfterDextV3_32 n p z).comp
          (actualSchurResolventFamilyAfterDextV3_32 n p z)))) z := by
  let Ep : Type := ParityPair n →L[ℂ] ParityPair n
  let nr : NormedRing Ep := ContinuousLinearMap.toNormedRing
  letI : NormedRing Ep := nr
  let un : NonUnitalNormedRing Ep := nr.toNonUnitalNormedRing
  letI : NonUnitalNormedRing Ep := un
  letI : NormedAddCommGroup Ep := un.toNormedAddCommGroup
  let na : NormedAlgebra ℂ Ep := ContinuousLinearMap.toNormedAlgebra
  letI : NormedAlgebra ℂ Ep := na
  let alg : Algebra ℂ Ep := na.toAlgebra
  letI : Algebra ℂ Ep := alg
  let ns : NormedSpace ℂ Ep := NormedAlgebra.toNormedSpace Ep
  letI : NormedSpace ℂ Ep := ns
  letI : Module ℂ Ep := ns.toModule
  letI : DistribMulAction ℂ Ep := ns.toModule.toDistribMulAction
  letI : DistribSMul ℂ Ep := DistribMulAction.toDistribSMul

  let D : ℂ → Ep := actualFreeResolventCenterExtensionV1_30 n
  let Q : Ep := freeResolventComplementaryProjectionTransported n
  let V : Ep := actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p
  let T : ℂ → Ep := fun w => Q.comp (V.comp (D w))
  let S : ℂ → Ep := fun w => actualComplementaryQVDJointInverseV5_30 n (w, p)
  let R : ℂ → Ep := actualSchurResolventFamilyAfterDextV3_32 n p
  let B : Ep := Q.comp (V.comp ((D z).comp (D z)))

  have hz2 : z ∈ Metric.ball (spectralCenter n) 2 := by
    change ‖z - spectralCenter n‖ ≤ 1 at hz
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖z - spectralCenter n‖ < 2
    linarith

  have hD := actualFreeResolventCenterExtension_hasFDerivAt_negativeSquareMinimumV4_33
    n z hz2
  have hTraw := actualComplementaryQVDParameter_hasFDerivAt_minimumV5_33
    n p z hz2
  have hTfunction : T = fun w : ℂ => Q.comp (V.comp (D w)) := by
    funext w
    rfl
  rw [← hTfunction] at hTraw
  let a' : Ep := Q.comp (V.comp (-(D z).comp (D z)))
  have hT : HasFDerivAt T (ContinuousLinearMap.toSpanSingleton ℂ a') z := by
    simpa only [a', D, Q, V] using hTraw

  have hSraw := rootActualSchurQVDInverse_hasFDerivAt_actualParentMinimum36V4
    radius hradius n hn hlarge p z hz hp₁ hp₂
  have hSmap :
      rootActualSchurQVDInverseDerivativeCLMMinimum36V4 n p z =
        ContinuousLinearMap.toSpanSingleton ℂ
          (-((S z).comp (B.comp (S z)))) := by
    simpa only [S, B, Q, V, D] using
      rootActualSchurInverseDerivativeSpanIdentity36MinimumV1 n p z
  have hS : HasFDerivAt S
      (ContinuousLinearMap.toSpanSingleton ℂ
        (-((S z).comp (B.comp (S z))))) z := by
    have hS' : HasFDerivAt S
        (rootActualSchurQVDInverseDerivativeCLMMinimum36V4 n p z) z := by
      simpa only [S] using hSraw
    exact hS'.congr_fderiv hSmap

  have hBassoc : B.comp (S z) =
      (T z).comp ((D z).comp (S z)) := by
    dsimp [B, T, D, Q, V]
    simp only [ContinuousLinearMap.comp_assoc]
  have hTvalue : actualComplementaryQVDJointParameterV5_30 n (z, p) = T z := by
    rw [actualSchurQVDParameterLocalFactorizationMinimumV1_33 n p z]
  have hresolventAlgebra :
      ((R z).comp (R z)) =
        ((D z).comp (D z)).comp (S z) +
          ((D z).comp (S z)).comp ((T z).comp ((D z).comp (S z))) := by
    simpa only [R, actualSchurResolventFamilyAfterDextV3_32, T, D, S, hTvalue] using
      (actualSchurResolventDerivativeCancellationIdentityV3_33
        radius hradius n hn hlarge p z hz hp₁ hp₂).symm
  have hRfactor : R = fun w : ℂ => (D w).comp (S w) := by
    funext w
    rfl

  have hGraw := hD.clm_comp hS
  have hGmap :
      (ContinuousLinearMap.compL ℂ (ParityPair n) (ParityPair n) (ParityPair n)
        (D z)).comp
          (ContinuousLinearMap.toSpanSingleton ℂ
            (-(S z).comp (B.comp (S z)))) +
        ((ContinuousLinearMap.compL ℂ (ParityPair n) (ParityPair n) (ParityPair n)).flip
          (S z)).comp
          (ContinuousLinearMap.toSpanSingleton ℂ
            (-(D z).comp (D z))) =
      ContinuousLinearMap.toSpanSingleton ℂ
        (-((R z).comp (R z))) := by
    apply ContinuousLinearMap.ext
    intro δ
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.map_smul]
    rw [hBassoc, hresolventAlgebra]
    simp only [ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.map_neg,
      ContinuousLinearMap.map_smul,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_neg, ContinuousLinearMap.neg_comp]
    rw [← smul_add]
    congr 1
    abel
  have hR := hGraw.congr_fderiv hGmap
  have hfunction : actualSchurResolventFamilyAfterDextV3_32 n p =
      fun w : ℂ => (D w).comp (S w) := by
    funext w
    rfl
  rw [hfunction]
  simpa only [R, D, S, actualSchurResolventFamilyAfterDextV3_32] using hR

end NlsGge.Schur

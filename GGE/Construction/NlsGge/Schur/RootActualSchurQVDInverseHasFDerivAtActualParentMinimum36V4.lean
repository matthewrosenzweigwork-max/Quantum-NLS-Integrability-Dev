import NlsGge.Schur.RootActualSchurOneSubQVDCanonicalDerivativeMinimum36V4
import NlsGge.Schur.ActualSchurSourceRingInverseFDerivMinimumV6_35
import NlsGge.Schur.ActualSchurQVDCompositionDerivativeMinimumV5_33
import NlsGge.Schur.ActualSchurQVDParameterLocalFactorizationMinimumV1_33
import NlsGge.Schur.ActualSchurCLMExplicitAlgebraTowerMulLeftRightMinimumV3_36
import NlsGge.Schur.ActualSchurQVDNegativeSpanSingletonIdentityMinimumV3_36
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
noncomputable section
open scoped Topology RightActions

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

/-- Named actual derivative CLM for the V5_30 total inverse. Keeping the
formula in a definition isolates the theorem type; the apply lemma directly
exposes both D factors and the source-order CLM composition. -/
noncomputable def rootActualSchurQVDInverseDerivativeCLMMinimum36V4
    (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) (z : ℂ) :
    ℂ →L[ℂ] (ParityPair n →L[ℂ] ParityPair n) := by
  let D : ℂ → ParityPair n →L[ℂ] ParityPair n :=
    actualFreeResolventCenterExtensionV1_30 n
  let Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n
  let V : ParityPair n →L[ℂ] ParityPair n :=
    actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p
  let S : ℂ → ParityPair n →L[ℂ] ParityPair n :=
    fun w => actualComplementaryQVDJointInverseV5_30 n (w, p)
  exact ContinuousLinearMap.toSpanSingleton ℂ
    (-((S z).comp ((Q.comp (V.comp ((D z).comp (D z)))).comp (S z))))

@[simp]
theorem rootActualSchurQVDInverseDerivativeCLMMinimum36V4_apply
    (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) (z : ℂ) (δ : ℂ) :
    rootActualSchurQVDInverseDerivativeCLMMinimum36V4 n p z δ =
      δ • (-((actualComplementaryQVDJointInverseV5_30 n (z, p)).comp
        (((freeResolventComplementaryProjectionTransported n).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
            ((actualFreeResolventCenterExtensionV1_30 n z).comp
              (actualFreeResolventCenterExtensionV1_30 n z)))).comp
          (actualComplementaryQVDJointInverseV5_30 n (z, p))))) := by
  simp [rootActualSchurQVDInverseDerivativeCLMMinimum36V4,
    ContinuousLinearMap.toSpanSingleton_apply]


set_option maxHeartbeats 400000 in
/-- The actual V5_30 total QVD inverse has its source-order two-Dext
Fréchet derivative on the unchanged signed spectral disk and independent
complex H¹ balls. Its named derivative CLM is exposed pointwise by the
preceding apply theorem as `-S (Q V D²) S`. -/
theorem rootActualSchurQVDInverse_hasFDerivAt_actualParentMinimum36V4
    (radius : ℝ) (hradius : 1 ≤ radius)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * radius ^ 2 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hp₁ : ‖p.1‖ ≤ radius) (hp₂ : ‖p.2‖ ≤ radius) :
    HasFDerivAt
      (fun w : ℂ => actualComplementaryQVDJointInverseV5_30 n (w, p))
      (rootActualSchurQVDInverseDerivativeCLMMinimum36V4 n p z) z := by
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
  let unSeminormed : NonUnitalSeminormedRing Ep := un.toNonUnitalSeminormedRing
  let tower : IsScalarTower ℂ Ep Ep := inferInstance
  letI : IsScalarTower ℂ Ep Ep := tower
  let smulComm : SMulCommClass ℂ Ep Ep := inferInstance
  let mulLR :=
    @ContinuousLinearMap.mulLeftRight ℂ inferInstance Ep unSeminormed ns tower smulComm
  let summable : HasSummableGeomSeries Ep := inferInstance

  -- This actual audited minimum is an import/build gate for the explicit
  -- algebra and multiplication-parent route used below.
  have hAlgebraTowerGate :=
    actualSchurCLMExplicitAlgebraTowerMulLeftRightMinimumV3_36 n

  let D : ℂ → Ep := actualFreeResolventCenterExtensionV1_30 n
  let Q : Ep := freeResolventComplementaryProjectionTransported n
  let V : Ep := actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p
  let T : ℂ → Ep := fun w => Q.comp (V.comp (D w))
  let S : ℂ → Ep := fun w => actualComplementaryQVDJointInverseV5_30 n (w, p)
  let B : Ep := Q.comp (V.comp ((D z).comp (D z)))

  have hz2 : z ∈ Metric.ball (spectralCenter n) 2 := by
    change ‖z - spectralCenter n‖ ≤ 1 at hz
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖z - spectralCenter n‖ < 2
    linarith

  have hTraw := actualComplementaryQVDParameter_hasFDerivAt_minimumV5_33
    n p z hz2
  have hTfunction : T = fun w : ℂ =>
      Q.comp (V.comp (D w)) := by
    funext w
    rfl
  rw [← hTfunction] at hTraw
  let a' : Ep := Q.comp (V.comp (-(D z).comp (D z)))
  have hT : HasFDerivAt T (ContinuousLinearMap.toSpanSingleton ℂ a') z := by
    simpa only [a', D, Q, V] using hTraw

  have hunitSource :
      @IsUnit Ep (actualSchurCLMSourceMonoidWithZeroV3_34 n).toMonoid
        (1 - T z) :=
    actualComplementaryQVDJointOneSubIsUnitV5_30
      radius hradius n hn hlarge z p hz hp₁ hp₂
  obtain ⟨uSource, huSource⟩ := hunitSource
  let uRing := actualSchurSourceUnitToRingParentV2_35 n uSource
  have hRingUnitValue : (uRing : Ep) = 1 - T z := by
    change (actualSchurSourceUnitToRingParentV2_35 n uSource : Ep) = 1 - T z
    rw [actualSchurSourceUnitToRingParentV2_35_coe]
    exact huSource
  have hSinv :
      ((uRing⁻¹ : @Units Ep
        (actualSchurCLMRingMonoidWithZeroV3_34 n).toMonoid) : Ep) = S z := by
    calc
      ((uRing⁻¹ : @Units Ep
          (actualSchurCLMRingMonoidWithZeroV3_34 n).toMonoid) : Ep) =
          @Ring.inverse Ep (actualSchurCLMRingMonoidWithZeroV3_34 n)
            (uRing : Ep) :=
        (@Ring.inverse_unit Ep
          (actualSchurCLMRingMonoidWithZeroV3_34 n) uRing).symm
      _ = @Ring.inverse Ep (actualSchurCLMRingMonoidWithZeroV3_34 n)
          (1 - T z) := by rw [hRingUnitValue]
      _ = @Ring.inverse Ep (actualSchurCLMSourceMonoidWithZeroV3_34 n)
          (1 - T z) :=
        (actualSchurParentedTotalInverseValueAgreementV2_35 n (1 - T z)).symm
      _ = S z := by
        simp only [S, T, actualComplementaryQVDJointInverseV5_30,
          actualComplementaryQVDJointParameterV5_30]
        rfl

  let ringInverse : Ep → Ep := fun Y =>
    @Ring.inverse Ep (actualSchurCLMRingMonoidWithZeroV3_34 n) Y
  have hRingExplicit : HasFDerivAt ringInverse
      (-mulLR
        (((uRing⁻¹ : @Units Ep
          (actualSchurCLMRingMonoidWithZeroV3_34 n).toMonoid) : Ep))
        (((uRing⁻¹ : @Units Ep
          (actualSchurCLMRingMonoidWithZeroV3_34 n).toMonoid) : Ep)))
      (uRing : Ep) := by
    exact @hasFDerivAt_ringInverse ℂ inferInstance Ep nr summable na uRing
  have hsameInverseFunctions :
      (fun Y : Ep =>
        @Ring.inverse Ep (actualSchurCLMSourceMonoidWithZeroV3_34 n) Y) =ᶠ[
          𝓝 (uRing : Ep)] ringInverse :=
    Filter.Eventually.of_forall fun Y =>
      actualSchurParentedTotalInverseValueAgreementV2_35 n Y
  have hsourceExplicit : HasFDerivAt
      (fun Y : Ep =>
        @Ring.inverse Ep (actualSchurCLMSourceMonoidWithZeroV3_34 n) Y)
      (-mulLR (S z) (S z))
      (uRing : Ep) := by
    simpa only [hSinv] using
      hRingExplicit.congr_of_eventuallyEq hsameInverseFunctions
  have hbase : HasFDerivAt
      (fun Y : Ep =>
        @Ring.inverse Ep (actualSchurCLMSourceMonoidWithZeroV3_34 n) Y)
      (-mulLR (S z) (S z))
      (1 - T z) := by
    simpa only [hRingUnitValue] using hsourceExplicit

  have hU : HasFDerivAt (fun w : ℂ => 1 - T w)
      (ContinuousLinearMap.toSpanSingleton ℂ (-a')) z := by
    simpa only [T, a', D, Q, V] using
      rootActualSchurOneSubQVD_hasFDerivAt_canonicalMinimum36V4 n p z hz2

  have hSraw := hbase.comp z hU
  have hSfunction : S = fun w : ℂ =>
      @Ring.inverse Ep (actualSchurCLMSourceMonoidWithZeroV3_34 n)
        (1 - T w) := by
    funext w
    simp only [S, T, actualComplementaryQVDJointInverseV5_30,
      actualComplementaryQVDJointParameterV5_30]
    rfl

  have ha' : a' = -B := by
    apply ContinuousLinearMap.ext
    intro x
    change Q (V (-(D z (D z x)))) = -(Q (V (D z (D z x))))
    rw [map_neg, map_neg]
  have hSvalue :
      (-mulLR (S z) (S z)) (-a') =
        -((S z).comp (B.comp (S z))) := by
    apply ContinuousLinearMap.ext
    intro x
    change -((mulLR (S z) (S z) (-a')) x) =
      -((S z).comp (B.comp (S z))) x
    rw [hAlgebraTowerGate.2 (S z) (S z) (-a') x, ha', neg_neg]
    rfl
  have hSmap :
      (-mulLR (S z) (S z)).comp
          (ContinuousLinearMap.toSpanSingleton ℂ (-a')) =
        rootActualSchurQVDInverseDerivativeCLMMinimum36V4 n p z := by
    apply ContinuousLinearMap.ext
    intro δ
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.map_smul]
    rw [hSvalue,
      rootActualSchurQVDInverseDerivativeCLMMinimum36V4_apply]
  have hS : HasFDerivAt S
      (rootActualSchurQVDInverseDerivativeCLMMinimum36V4 n p z) z := by
    rw [hSfunction]
    exact hSraw.congr_fderiv hSmap

  simpa only [S] using hS


end NlsGge.Schur

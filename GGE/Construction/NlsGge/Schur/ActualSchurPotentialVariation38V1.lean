import NlsGge.Schur.RootActualSchurQVDInverseHasFDerivAtActualParentMinimum36V4
import NlsGge.Schur.ActualSchurFGboundAfterResolventFactorizationV5_31
import NlsGge.Schur.ActualSchurAlphaBoundAfterDextV6_32
import NlsGge.Schur.ActualSchurCenterContraction38V1
import NlsGge.Schur.FreeResolventComplementaryInverseOnRangeActual
import NlsGge.Schur.FreeResolventComplementaryDQTransportAfterCoordinateRange
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Potential variation of the actual Schur effective operator (NEW-F04.04/.05)

Source: `paper/v2.tex` lines 1193-1201 (F:eq:variation).  For the actual
Dext-defined effective operator `A(z, p) = P V(p) P + P V(p) D S V(p) P`
(`S = (1 - Q V D)⁻¹`), the directional derivative in an arbitrary direction
`h` of the independent complex H¹ pair, at a base point `p` in the radius-`R`
balls and `z` in the signed spectral disk, is
`(P + G̃) V(h) (P + G)`, with `G = D S V P`, `G̃ = P V D S`.

Only the unit property of `1 - Q V(p) D` at the base point `t = 0` is used (units
of a Banach algebra are open, packaged in `hasFDerivAt_ringInverse`); no radius
enlargement is needed because `A` is the totalized formula by definition and the
derivative is taken at `t = 0`.
-/

set_option autoImplicit false
noncomputable section
open scoped Topology RightActions
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- Product-rule derivative of the totalized effective-operator formula along
the affine potential line `V + t W`, for an arbitrary differentiable inverse
family `S`. -/
theorem actualSchurEffectiveLine_hasDerivAt_generic38V1
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (P D V W : X →L[ℂ] X) (S : ℂ → X →L[ℂ] X) (S' : X →L[ℂ] X)
    (hS : HasDerivAt S S' 0) :
    HasDerivAt
      (fun t : ℂ => P.comp ((V + t • W).comp P) +
        P.comp ((V + t • W).comp ((D.comp (S t)).comp ((V + t • W).comp P))))
      (P.comp (W.comp P) + P.comp (W.comp ((D.comp (S 0)).comp (V.comp P))) +
        P.comp (V.comp ((D.comp S').comp (V.comp P))) +
        P.comp (V.comp ((D.comp (S 0)).comp (W.comp P)))) 0 := by
  have hVt : HasDerivAt (fun t : ℂ => V + t • W) W 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).smul_const W).const_add V
    simpa using this
  have hP : ∀ (A : ℂ → X →L[ℂ] X) (A' : X →L[ℂ] X), HasDerivAt A A' 0 →
      ∀ B : X →L[ℂ] X, HasDerivAt (fun t => B.comp (A t)) (B.comp A') 0 := by
    intro A A' hA B
    have := (hasDerivAt_const (0 : ℂ) B).clm_comp hA
    simpa using this
  have hPr : ∀ (A : ℂ → X →L[ℂ] X) (A' : X →L[ℂ] X), HasDerivAt A A' 0 →
      ∀ B : X →L[ℂ] X, HasDerivAt (fun t => (A t).comp B) (A'.comp B) 0 := by
    intro A A' hA B
    have := hA.clm_comp (hasDerivAt_const (0 : ℂ) B)
    simpa using this
  have h1 := hP _ _ (hPr _ _ hVt P) P
  have hVtP := hPr _ _ hVt P
  have hDS : HasDerivAt (fun t => D.comp (S t)) (D.comp S') 0 := hP _ _ hS D
  have hX := hDS.clm_comp hVtP
  have hY := hVt.clm_comp hX
  have hZ := hP _ _ hY P
  have := h1.add hZ
  convert this using 1
  simp only [zero_smul, add_zero, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_assoc]
  abel

/-- Affine dependence of `1 - Q (V + t W) D` on `t`, abstractly. -/
theorem actualSchurAffineLine_generic38V1
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (Q V W D : X →L[ℂ] X) :
    (∀ t : ℂ, Q.comp ((V + t • W).comp D) = Q.comp (V.comp D) + t • Q.comp (W.comp D)) ∧
    HasDerivAt (fun t : ℂ => (1 : X →L[ℂ] X) - (Q.comp (V.comp D) + t • Q.comp (W.comp D)))
      (-(Q.comp (W.comp D))) 0 ∧
    (1 : X →L[ℂ] X) - (Q.comp (V.comp D) + (0 : ℂ) • Q.comp (W.comp D)) =
      1 - Q.comp (V.comp D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  · have h0 := (((hasDerivAt_id (0 : ℂ)).smul_const (Q.comp (W.comp D))).const_add
      (Q.comp (V.comp D))).const_sub (1 : X →L[ℂ] X)
    simpa using h0
  · simp

/-- Entry functionals are differentiable along differentiable operator curves. -/
theorem actualSchurEntry_hasDerivAt_generic38V1
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ent : (X →L[ℂ] X) →L[ℂ] ℂ) {f : ℂ → X →L[ℂ] X} {f' : X →L[ℂ] X}
    (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun t : ℂ => ent (f t)) (ent f') 0 :=
  ent.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hf

set_option linter.style.haveILetI false in
set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Derivative of the actual total QVD inverse along the potential direction
`h`: `d/dt (1 - Q V(p + t h) D)⁻¹ |₀ = S (Q V(h) D) S`. -/
theorem actualSchurQVDInverse_hasDerivAt_potentialDirection38V1
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R)
    (h : ActualSchurEffectiveH1PairV3_30) :
    HasDerivAt
      (fun t : ℂ => actualComplementaryQVDJointInverseV5_30 n (z, p + t • h))
      ((actualComplementaryQVDJointInverseV5_30 n (z, p)).comp
        (((freeResolventComplementaryProjectionTransported n).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n h).comp
            (actualFreeResolventCenterExtensionV1_30 n z))).comp
          (actualComplementaryQVDJointInverseV5_30 n (z, p)))) 0 := by
  -- affine dependence of `Q V(p + t h) D` on `t`, in the standard instances
  obtain ⟨hTlineAbs, hUstd, hT0⟩ := actualSchurAffineLine_generic38V1
    (freeResolventComplementaryProjectionTransported n)
    (actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p)
    (actualParityPairPotentialParameterAfterScalarWrapperCLM23 n h)
    (actualFreeResolventCenterExtensionV1_30 n z)
  have hTline : ∀ t : ℂ,
      actualComplementaryQVDJointParameterV5_30 n (z, p + t • h) =
        actualComplementaryQVDJointParameterV5_30 n (z, p) +
          t • (freeResolventComplementaryProjectionTransported n).comp
            ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n h).comp
              (actualFreeResolventCenterExtensionV1_30 n z)) := by
    intro t
    have hV : actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (p + t • h) =
        actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p +
          t • actualParityPairPotentialParameterAfterScalarWrapperCLM23 n h := by
      rw [map_add, map_smul]
    change (freeResolventComplementaryProjectionTransported n).comp
      ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (p + t • h)).comp
        (actualFreeResolventCenterExtensionV1_30 n z)) = _
    rw [hV, hTlineAbs t]
    rfl
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
  let unSeminormed : NonUnitalSeminormedRing Ep := un.toNonUnitalSeminormedRing
  let tower : IsScalarTower ℂ Ep Ep := inferInstance
  letI : IsScalarTower ℂ Ep Ep := tower
  let smulComm : SMulCommClass ℂ Ep Ep := inferInstance
  let mulLR :=
    @ContinuousLinearMap.mulLeftRight ℂ inferInstance Ep unSeminormed ns tower smulComm
  let summable : HasSummableGeomSeries Ep := inferInstance
  have hAlgebraTowerGate :=
    actualSchurCLMExplicitAlgebraTowerMulLeftRightMinimumV3_36 n
  let D : Ep := actualFreeResolventCenterExtensionV1_30 n z
  let Q : Ep := freeResolventComplementaryProjectionTransported n
  let V : Ep := actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p
  let W : Ep := actualParityPairPotentialParameterAfterScalarWrapperCLM23 n h
  let T0 : Ep := Q.comp (V.comp D)
  let a : Ep := Q.comp (W.comp D)
  let S : Ep := actualComplementaryQVDJointInverseV5_30 n (z, p)
  have hunitSource :
      @IsUnit Ep (actualSchurCLMSourceMonoidWithZeroV3_34 n).toMonoid
        (1 - T0) :=
    actualComplementaryQVDJointOneSubIsUnitV5_30
      R hR n hn hlarge z p hz hp₁ hp₂
  obtain ⟨uSource, huSource⟩ := hunitSource
  let uRing := actualSchurSourceUnitToRingParentV2_35 n uSource
  have hRingUnitValue : (uRing : Ep) = 1 - T0 := by
    change (actualSchurSourceUnitToRingParentV2_35 n uSource : Ep) = 1 - T0
    rw [actualSchurSourceUnitToRingParentV2_35_coe]
    exact huSource
  have hSinv :
      ((uRing⁻¹ : @Units Ep
        (actualSchurCLMRingMonoidWithZeroV3_34 n).toMonoid) : Ep) = S := by
    calc
      ((uRing⁻¹ : @Units Ep
          (actualSchurCLMRingMonoidWithZeroV3_34 n).toMonoid) : Ep) =
          @Ring.inverse Ep (actualSchurCLMRingMonoidWithZeroV3_34 n)
            (uRing : Ep) :=
        (@Ring.inverse_unit Ep
          (actualSchurCLMRingMonoidWithZeroV3_34 n) uRing).symm
      _ = @Ring.inverse Ep (actualSchurCLMRingMonoidWithZeroV3_34 n)
          (1 - T0) := by rw [hRingUnitValue]
      _ = @Ring.inverse Ep (actualSchurCLMSourceMonoidWithZeroV3_34 n)
          (1 - T0) :=
        (actualSchurParentedTotalInverseValueAgreementV2_35 n (1 - T0)).symm
      _ = S := by
        simp only [S, T0, actualComplementaryQVDJointInverseV5_30,
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
      (-mulLR S S) (uRing : Ep) := by
    simpa only [hSinv] using
      hRingExplicit.congr_of_eventuallyEq hsameInverseFunctions
  have hbase : HasFDerivAt
      (fun Y : Ep =>
        @Ring.inverse Ep (actualSchurCLMSourceMonoidWithZeroV3_34 n) Y)
      (-mulLR S S) (1 - T0) := by
    simpa only [hRingUnitValue] using hsourceExplicit
  -- the affine line `1 - Q V(p + t h) D = (1 - T0) - t a`
  let Tfun : ℂ → Ep := fun t => 1 - (T0 + t • a)
  have hU : HasDerivAt Tfun (-a) 0 := hUstd
  have hTfun0 : Tfun 0 = 1 - T0 := hT0
  have hbase' : HasFDerivAt
      (fun Y : Ep =>
        @Ring.inverse Ep (actualSchurCLMSourceMonoidWithZeroV3_34 n) Y)
      (-mulLR S S) (Tfun 0) := by
    rw [hTfun0]
    exact hbase
  have hcomp := hbase'.comp_hasDerivAt (0 : ℂ) hU
  have hfun : (fun t : ℂ => actualComplementaryQVDJointInverseV5_30 n (z, p + t • h)) =
      (fun Y : Ep =>
        @Ring.inverse Ep (actualSchurCLMSourceMonoidWithZeroV3_34 n) Y) ∘ Tfun := by
    funext t
    have hT := hTline t
    change Ring.inverse (1 - actualComplementaryQVDJointParameterV5_30 n (z, p + t • h)) = _
    rw [hT]
    rfl
  have hvalue : (-mulLR S S) (-a) = S.comp (a.comp S) := by
    apply ContinuousLinearMap.ext
    intro x
    change -((mulLR S S (-a)) x) = (S.comp (a.comp S)) x
    rw [hAlgebraTowerGate.2 S S (-a) x]
    simp only [mul_neg, neg_mul, neg_apply, neg_neg]
    rfl
  rw [hvalue] at hcomp
  rw [hfun]
  exact hcomp


set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- F:eq:variation (operator form): the derivative of the actual effective
operator along the independent complex H¹ direction `h` at `t = 0` is
`(P + G̃) V(h) (P + G)`. -/
theorem actualSchurEffective_hasDerivAt_potentialVariation38V1
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R)
    (h : ActualSchurEffectiveH1PairV3_30) :
    HasDerivAt
      (fun t : ℂ => actualSchurEffectiveOperatorAfterDextV3_30 n (z, p + t • h))
      (((resonantParityPair n) + actualSchurGreenRowV5_31 n z p hz).comp
        ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n h).comp
          ((resonantParityPair n) + actualSchurGreenColumnV5_31 n z p hz))) 0 := by
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  let Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n
  let V : ParityPair n →L[ℂ] ParityPair n :=
    actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p
  let W : ParityPair n →L[ℂ] ParityPair n :=
    actualParityPairPotentialParameterAfterScalarWrapperCLM23 n h
  let D : ParityPair n →L[ℂ] ParityPair n := actualFreeResolventCenterExtensionV1_30 n z
  let S : ParityPair n →L[ℂ] ParityPair n :=
    actualComplementaryQVDJointInverseV5_30 n (z, p)
  let Sfun : ℂ → ParityPair n →L[ℂ] ParityPair n :=
    fun t => actualComplementaryQVDJointInverseV5_30 n (z, p + t • h)
  let S' : ParityPair n →L[ℂ] ParityPair n := S.comp ((Q.comp (W.comp D)).comp S)
  have hSder : HasDerivAt Sfun S' 0 :=
    actualSchurQVDInverse_hasDerivAt_potentialDirection38V1
      R hR n hn hlarge p z hz hp₁ hp₂ h
  have hgen := actualSchurEffectiveLine_hasDerivAt_generic38V1 P D V W Sfun S' hSder
  have hS0 : Sfun 0 = S := by simp [Sfun, S]
  rw [hS0] at hgen
  have hD : D = freeResolventParityPair n z hz :=
    actualFreeResolventCenterExtension_eq_actualV1_30 n z hz
  -- Green row and column in terms of `D S`
  have hrow : actualSchurGreenRowV5_31 n z p hz = P.comp (V.comp (D.comp S)) := by
    let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
    let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
    let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
    let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
    have hV : V = coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n := by
      dsimp [V, u₁, u₂, hu₁, hu₂]
      exact actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n p
    change P.comp ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp
        ((freeResolventParityPair n z hz).comp
          (actualComplementaryQVDJointInverseV5_30 n (z, p)))) = _
    rw [← hV, ← hD]
  have hcolumn : actualSchurGreenColumnV5_31 n z p hz = (D.comp S).comp (V.comp P) := by
    let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
    let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
    let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
    let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
    have hV : V = coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n := by
      dsimp [V, u₁, u₂, hu₁, hu₂]
      exact actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n p
    change ((freeResolventParityPair n z hz).comp
        (actualComplementaryQVDJointInverseV5_30 n (z, p))).comp
          ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp P) = _
    rw [← hV, ← hD]
  -- `D S Q = D S`
  have htwo := actualComplementaryQVDJointInverseV5_30_twoSided
    R hR n hn hlarge z p hz hp₁ hp₂
  have hQQ : Q.comp Q = Q := freeResolventComplementaryProjectionTransported_idempotent_actual22 n
  have hDQ : D.comp Q = D := by
    rw [hD]
    exact freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange n z hz
  have hSQ : S.comp Q = Q.comp S := by
    let K : ParityPair n →L[ℂ] ParityPair n := Q.comp (V.comp D)
    have hQK : Q.comp K = K := by
      change Q.comp (Q.comp (V.comp D)) = Q.comp (V.comp D)
      rw [← ContinuousLinearMap.comp_assoc, hQQ]
    have hKQ : K.comp Q = K := by
      change (Q.comp (V.comp D)).comp Q = Q.comp (V.comp D)
      rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, hDQ]
    have h1 : S.comp (1 - K) = 1 := htwo.1
    have h2 : (1 - K).comp S = 1 := htwo.2
    have hcomm : Q.comp (1 - K) = (1 - K).comp Q := by
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, hQK, hKQ,
        ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id,
        ContinuousLinearMap.id_comp]
    calc S.comp Q = (S.comp Q).comp ((1 - K).comp S) := by
          rw [h2, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
      _ = S.comp ((Q.comp (1 - K)).comp S) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = S.comp (((1 - K).comp Q).comp S) := by rw [hcomm]
      _ = (S.comp (1 - K)).comp (Q.comp S) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = Q.comp S := by
          rw [h1, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  have hDSQ (y : ParityPair n) : D (S (Q y)) = D (S y) := by
    have h := congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T (S y)) hDQ
    have h2 := congrArg (fun T : ParityPair n →L[ℂ] ParityPair n => T y) hSQ
    simp only [ContinuousLinearMap.comp_apply] at h h2
    rw [h2]
    exact h
  have hfun : (fun t : ℂ => actualSchurEffectiveOperatorAfterDextV3_30 n (z, p + t • h)) =
      (fun t : ℂ => P.comp ((V + t • W).comp P) +
        P.comp ((V + t • W).comp ((D.comp (Sfun t)).comp ((V + t • W).comp P)))) := by
    funext t
    have hV : actualParityPairPotentialParameterAfterScalarWrapperCLM23 n (p + t • h) =
        V + t • W := by
      simp only [V, W, map_add, map_smul]
    simp only [actualSchurEffectiveOperatorAfterDextV3_30, hV]
    rfl
  rw [hfun]
  rw [hrow, hcolumn]
  convert hgen using 1
  apply ContinuousLinearMap.ext
  intro x
  have hS'apply (y : ParityPair n) : D (S' y) = D (S (W (D (S y)))) := by
    change D (S (Q (W (D (S y))))) = _
    exact hDSQ _
  simp only [ContinuousLinearMap.comp_apply, add_apply, map_add,
    hS'apply]
  abel

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- F:eq:variation (entry form): every actual Schur coefficient has the
directional derivative `⟪e_i, (P + G̃) V(h) (P + G) e_j⟫` at `t = 0`. -/
theorem actualSchurCoefficient_hasDerivAt_potentialVariation38V1
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R)
    (h : ActualSchurEffectiveH1PairV3_30) (i j : Bool × Sector n) :
    HasDerivAt
      (fun t : ℂ => actualSchurCoefficientAfterDext31 n i j (z, p + t • h))
      (actualSchurEntryFunctional31 n i j
        (((resonantParityPair n) + actualSchurGreenRowV5_31 n z p hz).comp
          ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n h).comp
            ((resonantParityPair n) + actualSchurGreenColumnV5_31 n z p hz)))) 0 := by
  have hmain := actualSchurEffective_hasDerivAt_potentialVariation38V1
    R hR n hn hlarge z hz p hp₁ hp₂ h
  exact actualSchurEntry_hasDerivAt_generic38V1 (actualSchurEntryFunctional31 n i j) hmain

end NlsGge.Schur

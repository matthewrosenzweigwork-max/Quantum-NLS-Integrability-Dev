import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Schur.ActualSchurPotentialVariation38V1
import NlsGge.Schur.ActualSchurEffectiveJointAnalyticAfterDextV3_30
import NlsGge.Schur.ActualSchurFGboundAfterResolventFactorizationV5_31
import NlsGge.Schur.ActualSchurEffectiveDerivativeSupportV1_32
import NlsGge.Schur.ActualComplementaryQVDJointInverseAndEqualDiagonalV5_30
import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30
import NlsGge.Schur.ActualParityPairPotentialParameterAfterScalarWrapper23
import NlsGge.Schur.FreeResolventComplementaryQDTransportAfterCoordinateRange
import NlsGge.Schur.FreeResolventComplementaryDQTransportAfterCoordinateRange
import NlsGge.Schur.FreeResolventComplementaryInverseOnRangeActual

                                                                                                                    
                                                                                                                     
                                                                                                                      
                                                                                                                 
                                                                                                      
                                                                                                                       
                                                                                                                         
                                                                                                                        
                                                                                                                          
                                                                                                                    
                                                                                                                     
                                                                                           
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
open scoped Topology
namespace NlsGge.ThirdConsultation.S

/-- The production green row is the shared-host `greenRow`. -/
theorem s029_greenRow_eq (n : ℤ) (z : ℂ) (p : SchurPair) (hz : z ∈ spectralDisk n) :
    actualSchurGreenRowV5_31 n z p hz = greenRow n z p := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  have hV : actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p =
      coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n := by
    dsimp [u₁, u₂, hu₁, hu₂]
    exact actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n p
  have hD : actualFreeResolventCenterExtensionV1_30 n z = freeResolventParityPair n z hz :=
    actualFreeResolventCenterExtension_eq_actualV1_30 n z hz
  change (resonantParityPair n).comp ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp
      ((freeResolventParityPair n z hz).comp (actualComplementaryQVDJointInverseV5_30 n (z, p)))) =
    (resonantParityPair n).comp ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
      ((actualFreeResolventCenterExtensionV1_30 n z).comp
        (actualComplementaryQVDJointInverseV5_30 n (z, p))))
  rw [← hV, ← hD]

/-- The production green column is the shared-host `greenColumn`. -/
theorem s029_greenColumn_eq (n : ℤ) (z : ℂ) (p : SchurPair) (hz : z ∈ spectralDisk n) :
    actualSchurGreenColumnV5_31 n z p hz = greenColumn n z p := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  have hV : actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p =
      coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n := by
    dsimp [u₁, u₂, hu₁, hu₂]
    exact actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n p
  have hD : actualFreeResolventCenterExtensionV1_30 n z = freeResolventParityPair n z hz :=
    actualFreeResolventCenterExtension_eq_actualV1_30 n z hz
  change ((freeResolventParityPair n z hz).comp (actualComplementaryQVDJointInverseV5_30 n (z, p))).comp
      ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp (resonantParityPair n)) =
    ((actualFreeResolventCenterExtensionV1_30 n z).comp
        (actualComplementaryQVDJointInverseV5_30 n (z, p))).comp
      ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp (resonantParityPair n))
  rw [← hV, ← hD]

/-- Fixed-z Frechet differentiability of the actual effective operator in the H1 pair on the
radius-R ball, from the production joint analyticity on the domain. -/
theorem s029_diff (R : ℝ) (hR : 1 ≤ R) (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n) (p : SchurPair) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    DifferentiableAt ℂ (effectiveAt n z) p := by
  have hAt := analyticOnNhd_actualSchurEffectiveOperatorAfterDextV3_30 R hR n hn hlarge (z, p)
    ⟨hz, hp₁, hp₂⟩
  have hpair : DifferentiableAt ℂ (fun q : SchurPair => (z, q)) p :=
    (differentiableAt_const z).prodMk differentiableAt_id
  exact hAt.differentiableAt.comp p hpair

/-- Directional derivative of the effective operator in an arbitrary actual H1 direction. -/
theorem s029_line (R : ℝ) (hR : 1 ≤ R) (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n) (p : SchurPair) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R)
    (h : SchurPair) :
    HasDerivAt (fun t : ℂ => effectiveAt n z (p + t • h))
      (((resonantParityPair n) + greenRow n z p).comp
        ((potentialAt n h).comp ((resonantParityPair n) + greenColumn n z p))) 0 := by
  have hprod := actualSchurEffective_hasDerivAt_potentialVariation38V1 R hR n hn hlarge z hz p hp₁ hp₂ h
  rw [← s029_greenRow_eq n z p hz, ← s029_greenColumn_eq n z p hz]
  exact hprod

/-- Chain rule along the line `t |-> p + t h` for a Frechet derivative at `p` (generic). -/
theorem s029_chain {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (g : E → F) (g' : E →L[ℂ] F) (p h : E)
    (hg : HasFDerivAt g g' p) :
    HasDerivAt (fun t : ℂ => g (p + t • h)) (g' h) 0 := by
  have hl : HasDerivAt (fun t : ℂ => p + t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add p
  have hg2 : HasFDerivAt g g' (p + (0 : ℂ) • h) := by
    rw [zero_smul, add_zero]
    exact hg
  exact hg2.comp_hasDerivAt (0 : ℂ) hl

/-- Uniqueness of the Frechet derivative from the line derivative (generic, abstract spaces). -/
theorem s029_fderiv_unique {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (g : E → F) (p h : E)
    (hd : DifferentiableAt ℂ g p) (A : F)
    (hA : HasDerivAt (fun t : ℂ => g (p + t • h)) A 0) :
    fderiv ℂ g p h = A :=
  (hA.unique (s029_chain g (fderiv ℂ g p) p h hd.hasFDerivAt)).symm

/-- Frechet derivative in the potential direction `h` (the first conjunct of the S-029 head). -/
theorem s029_fderiv (R : ℝ) (hR : 1 ≤ R) (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n) (p : SchurPair) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R)
    (h : SchurPair) :
    fderiv ℂ (effectiveAt n z) p h =
      ((resonantParityPair n) + greenRow n z p).comp
        ((potentialAt n h).comp ((resonantParityPair n) + greenColumn n z p)) :=
  s029_fderiv_unique (E := SchurPair) (F := ParityPair n →L[ℂ] ParityPair n)
    (effectiveAt n z) p h (s029_diff R hR n hn hlarge z hz p hp₁ hp₂) _
    (s029_line R hR n hn hlarge z hz p hp₁ hp₂ h)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Line derivative of the total inverse `Ring.inverse (1 - Q (V + t W) D)` at `t = 0` for an
ARBITRARY bounded direction `W` at a source-unit base point. Production argument of
actualSchurQVDInverse_hasDerivAt_potentialDirection38V1 (ActualSchurPotentialVariation38V1), generalized
from `W = CLM23 h` to any `W`; the statement's derivative is `S (Q W D) S` with `S = (1 - Q V D)⁻¹`. -/
theorem s029_ringInverse_line (n : ℤ) (Q V W D : ParityPair n →L[ℂ] ParityPair n)
    (hunitSource : @IsUnit (ParityPair n →L[ℂ] ParityPair n)
      (actualSchurCLMSourceMonoidWithZeroV3_34 n).toMonoid (1 - Q.comp (V.comp D))) :
    HasDerivAt (fun t : ℂ => Ring.inverse (1 - Q.comp ((V + t • W).comp D)))
      ((Ring.inverse (1 - Q.comp (V.comp D))).comp
        ((Q.comp (W.comp D)).comp (Ring.inverse (1 - Q.comp (V.comp D))))) 0 := by
  obtain ⟨hTlineAbs, hUstd, hT0⟩ := actualSchurAffineLine_generic38V1 Q V W D
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
  let T0 : Ep := Q.comp (V.comp D)
  let a : Ep := Q.comp (W.comp D)
  let S : Ep := Ring.inverse (1 - T0)
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
      _ = S := rfl
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
  have hfun : (fun t : ℂ => Ring.inverse (1 - Q.comp ((V + t • W).comp D))) =
      (fun Y : Ep =>
        @Ring.inverse Ep (actualSchurCLMSourceMonoidWithZeroV3_34 n) Y) ∘ Tfun := by
    funext t
    rw [hTlineAbs t]
    rfl
  have hvalue : (-mulLR S S) (-a) = S.comp (a.comp S) := by
    apply ContinuousLinearMap.ext
    intro x
    change -((mulLR S S (-a)) x) = (S.comp (a.comp S)) x
    rw [hAlgebraTowerGate.2 S S (-a) x]
    simp only [mul_neg, neg_mul, ContinuousLinearMap.neg_apply, neg_neg]
    try rfl
  rw [hvalue] at hcomp
  rw [hfun]
  exact hcomp

/-- Joint identity `D S Q = D S` for the actual complementary inverse. -/
theorem s029_DSQ (R : ℝ) (hR : 1 ≤ R) (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (hz : z ∈ spectralDisk n) (p : SchurPair) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    (actualFreeResolventCenterExtensionV1_30 n z).comp
      ((actualComplementaryQVDJointInverseV5_30 n (z, p)).comp
        (freeResolventComplementaryProjectionTransported n)) =
    (actualFreeResolventCenterExtensionV1_30 n z).comp
      (actualComplementaryQVDJointInverseV5_30 n (z, p)) := by
  have htwo := actualComplementaryQVDJointInverseV5_30_twoSided R hR n hn hlarge z p hz hp₁ hp₂
  have hQQ : (freeResolventComplementaryProjectionTransported n).comp
      (freeResolventComplementaryProjectionTransported n) =
      freeResolventComplementaryProjectionTransported n :=
    freeResolventComplementaryProjectionTransported_idempotent_actual22 n
  have hDQ : (actualFreeResolventCenterExtensionV1_30 n z).comp
      (freeResolventComplementaryProjectionTransported n) =
      actualFreeResolventCenterExtensionV1_30 n z := by
    rw [actualFreeResolventCenterExtension_eq_actualV1_30 n z hz]
    exact freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange n z hz
  have hSQ : (actualComplementaryQVDJointInverseV5_30 n (z, p)).comp
      (freeResolventComplementaryProjectionTransported n) =
      (freeResolventComplementaryProjectionTransported n).comp
        (actualComplementaryQVDJointInverseV5_30 n (z, p)) := by
    let Q : ParityPair n →L[ℂ] ParityPair n := freeResolventComplementaryProjectionTransported n
    let S : ParityPair n →L[ℂ] ParityPair n := actualComplementaryQVDJointInverseV5_30 n (z, p)
    let K : ParityPair n →L[ℂ] ParityPair n :=
      Q.comp ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
        (actualFreeResolventCenterExtensionV1_30 n z))
    have hQK : Q.comp K = K := by
      change Q.comp (Q.comp _) = Q.comp _
      rw [← ContinuousLinearMap.comp_assoc, hQQ]
    have hKQ : K.comp Q = K := by
      change (Q.comp ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
        (actualFreeResolventCenterExtensionV1_30 n z))).comp Q = _
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
  rw [hSQ, ← ContinuousLinearMap.comp_assoc, hDQ]

/-- The base unit in the S-chain source monoid (isolated so that its defeq check is a separate declaration). -/
theorem s029_unitS (R : ℝ) (hR : 1 ≤ R) (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : SchurPair) (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    @IsUnit (ParityPair n →L[ℂ] ParityPair n)
      (actualSchurCLMSourceMonoidWithZeroV3_34 n).toMonoid
      (1 - (freeResolventComplementaryProjectionTransported n).comp
        ((actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p).comp
          (actualFreeResolventCenterExtensionV1_30 n z))) :=
  actualComplementaryQVDJointOneSubIsUnitV5_30 R hR n hn hlarge z p hz hp₁ hp₂


/-- S-029 first head: the directional derivative and the Frechet derivative of the exact Schur
matrix in an arbitrary actual H1 potential direction. -/
theorem schur_potential_fderiv :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (n : ℤ) (z : ℂ) (p : SchurPair),
      schurParameterDomain K R n z p → ∀ h : SchurPair,
      HasDerivAt (fun t : ℂ => effectiveAt n z (p + t • h))
        (((resonantParityPair n) + greenRow n z p).comp
          ((potentialAt n h).comp ((resonantParityPair n) + greenColumn n z p))) 0 ∧
      fderiv ℂ (effectiveAt n z) p h =
        ((resonantParityPair n) + greenRow n z p).comp
          ((potentialAt n h).comp ((resonantParityPair n) + greenColumn n z p)) := by
  refine ⟨max 1 (4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R n z p hdom h
  obtain ⟨hR, hn0, hK, hz, hp₁, hp₂⟩ := hdom
  have hn : 1 ≤ |(n : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast h1
  have hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg R)) hK
  exact ⟨s029_line R hR n hn hlarge z hz p hp₁ hp₂ h,
    s029_fderiv R hR n hn hlarge z hz p hp₁ hp₂ h⟩

/-- Pure algebra for the operator head: the four-term derivative of the generic product rule equals
`(P + P V R) H (P + R V P)` with `R = D S0`, using `D S0 Q = D S0`. -/
theorem s029_op_value (n : ℤ) (P V H D S0 Q : ParityPair n →L[ℂ] ParityPair n)
    (hDSQ : (D.comp S0).comp Q = D.comp S0) :
    P.comp (H.comp P) +
      P.comp (H.comp ((D.comp S0).comp (V.comp P))) +
      P.comp (V.comp ((D.comp (S0.comp ((Q.comp (H.comp D)).comp S0))).comp (V.comp P))) +
      P.comp (V.comp ((D.comp S0).comp (H.comp P))) =
    (P + P.comp (V.comp (D.comp S0))).comp (H.comp (P + (D.comp S0).comp (V.comp P))) := by
  have e : D.comp (S0.comp ((Q.comp (H.comp D)).comp S0)) =
      ((D.comp S0).comp Q).comp (H.comp (D.comp S0)) := by
    simp only [ContinuousLinearMap.comp_assoc]
  rw [e, hDSQ]
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_assoc]
  abel

/-- Core operator-direction derivative, in abstract bounded operators (no concrete resolvent unfolding). -/
theorem s029_op_core (n : ℤ) (P Q V D H : ParityPair n →L[ℂ] ParityPair n)
    (hunit : @IsUnit (ParityPair n →L[ℂ] ParityPair n)
      (actualSchurCLMSourceMonoidWithZeroV3_34 n).toMonoid (1 - Q.comp (V.comp D)))
    (hDSQ : (D.comp (Ring.inverse (1 - Q.comp (V.comp D)))).comp Q =
      D.comp (Ring.inverse (1 - Q.comp (V.comp D)))) :
    HasDerivAt
      (fun t : ℂ => P.comp ((V + t • H).comp P) +
        P.comp ((V + t • H).comp
          ((D.comp (Ring.inverse (1 - Q.comp ((V + t • H).comp D)))).comp
            ((V + t • H).comp P))))
      ((P + P.comp (V.comp (D.comp (Ring.inverse (1 - Q.comp (V.comp D)))))).comp
        (H.comp (P + (D.comp (Ring.inverse (1 - Q.comp (V.comp D)))).comp (V.comp P)))) 0 := by
  have hSder := s029_ringInverse_line n Q V H D hunit
  have hgen := actualSchurEffectiveLine_hasDerivAt_generic38V1 P D V H
    (fun t : ℂ => Ring.inverse (1 - Q.comp ((V + t • H).comp D)))
    ((Ring.inverse (1 - Q.comp (V.comp D))).comp
      ((Q.comp (H.comp D)).comp (Ring.inverse (1 - Q.comp (V.comp D))))) hSder
  have hV0 : V + (0 : ℂ) • H = V := by
    ext x
    simp
  have hS0 : Ring.inverse (1 - Q.comp ((V + (0 : ℂ) • H).comp D)) =
      Ring.inverse (1 - Q.comp (V.comp D)) := by
    rw [hV0]
  beta_reduce at hgen
  rw [hS0] at hgen
  exact hgen.congr_deriv
    (s029_op_value n P V H D (Ring.inverse (1 - Q.comp (V.comp D))) Q hDSQ)

/-- Unfolding the effective operator along the operator line (shallow delta only). -/
theorem s029_opEff_fun (n : ℤ) (z : ℂ) (p : SchurPair) (H : ParityPair n →L[ℂ] ParityPair n) :
    (fun t : ℂ => operatorEffectiveAt n z (potentialAt n p + t • H)) =
      (fun t : ℂ => (resonantParityPair n).comp (((potentialAt n p) + t • H).comp (resonantParityPair n)) +
        (resonantParityPair n).comp (((potentialAt n p) + t • H).comp
          (((actualFreeResolventCenterExtensionV1_30 n z).comp
            (Ring.inverse (1 - (freeResolventComplementaryProjectionTransported n).comp
              (((potentialAt n p) + t • H).comp (actualFreeResolventCenterExtensionV1_30 n z))))).comp
            (((potentialAt n p) + t • H).comp (resonantParityPair n))))) := rfl

/-- Unfolding the Green row and column around an operator direction (shallow delta only). -/
theorem s029_green_deriv (n : ℤ) (z : ℂ) (p : SchurPair) (H : ParityPair n →L[ℂ] ParityPair n) :
    (((resonantParityPair n) + greenRow n z p).comp
          (H.comp ((resonantParityPair n) + greenColumn n z p))) =
      ((resonantParityPair n + (resonantParityPair n).comp ((potentialAt n p).comp
          ((actualFreeResolventCenterExtensionV1_30 n z).comp
            (Ring.inverse (1 - (freeResolventComplementaryProjectionTransported n).comp
              ((potentialAt n p).comp (actualFreeResolventCenterExtensionV1_30 n z))))))).comp
        (H.comp (resonantParityPair n +
          ((actualFreeResolventCenterExtensionV1_30 n z).comp
            (Ring.inverse (1 - (freeResolventComplementaryProjectionTransported n).comp
              ((potentialAt n p).comp (actualFreeResolventCenterExtensionV1_30 n z))))).comp
            ((potentialAt n p).comp (resonantParityPair n))))) := rfl

/-- S-029 second head: the derivative of the exact Schur matrix along an arbitrary bounded
operator direction (the full arbitrary bounded-operator clause). -/
theorem schur_potential_operator_variation :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (n : ℤ) (z : ℂ) (p : SchurPair),
      schurParameterDomain K R n z p →
      ∀ H : ParityPair n →L[ℂ] ParityPair n,
      HasDerivAt
        (fun t : ℂ => operatorEffectiveAt n z (potentialAt n p + t • H))
        (((resonantParityPair n) + greenRow n z p).comp
          (H.comp ((resonantParityPair n) + greenColumn n z p))) 0 := by
  refine ⟨max 1 (4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R n z p hdom H
  obtain ⟨hR, hn0, hK, hz, hp₁, hp₂⟩ := hdom
  have hn : 1 ≤ |(n : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast h1
  have hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg R)) hK
  have hunit := s029_unitS R hR n hn hlarge z p hz hp₁ hp₂
  have hDS := s029_DSQ R hR n hn hlarge z hz p hp₁ hp₂
  have hDSQ : ((actualFreeResolventCenterExtensionV1_30 n z).comp
      (Ring.inverse (1 - (freeResolventComplementaryProjectionTransported n).comp
        ((potentialAt n p).comp (actualFreeResolventCenterExtensionV1_30 n z))))).comp
      (freeResolventComplementaryProjectionTransported n) =
      (actualFreeResolventCenterExtensionV1_30 n z).comp
        (Ring.inverse (1 - (freeResolventComplementaryProjectionTransported n).comp
          ((potentialAt n p).comp (actualFreeResolventCenterExtensionV1_30 n z)))) := by
    rw [ContinuousLinearMap.comp_assoc]
    exact hDS
  have hcore := s029_op_core n (resonantParityPair n)
    (freeResolventComplementaryProjectionTransported n) (potentialAt n p)
    (actualFreeResolventCenterExtensionV1_30 n z) H hunit hDSQ
  rw [s029_opEff_fun, s029_green_deriv]
  exact hcore

end NlsGge.ThirdConsultation.S

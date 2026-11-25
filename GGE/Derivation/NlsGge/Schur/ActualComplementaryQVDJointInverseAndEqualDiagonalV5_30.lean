import NlsGge.Schur.ActualComplementaryQVDJointInverseAnalyticAfterDextV5_30
import NlsGge.Schur.ActualSchurTransposeIdentityMinimumV1_30
import NlsGge.Schur.ActualSchurTransposeFixedTransportedFactorsV6_24
import NlsGge.Schur.ActualPairTransposeAddSubPrerequisitesV2_25
import NlsGge.Schur.ActualCoordinateTransposeMatrixEntryV2_24
import NlsGge.Schur.ComplementaryResolventCanonicalFormulaAfterMonoidPrerequisite

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Analysis NlsGge.Pilot

abbrev ActualH1PairJointSchurV5_30 :=
  WeightedHilbert (sobolevModeWeight (1 : ℝ)) ×
    WeightedHilbert (sobolevModeWeight (1 : ℝ))

abbrev ActualSchurPairEndomorphismV5_30 (n : ℤ) :=
  ParityPair n →L[ℂ] ParityPair n

abbrev ActualSchurCoordinateEndomorphismV5_30 (n : ℤ) :=
  SectorSquare n →L[ℂ] SectorSquare n

def actualSchurEndomorphismToSquareV5_30 (n : ℤ)
    (T : ActualSchurPairEndomorphismV5_30 n) :
    ActualSchurCoordinateEndomorphismV5_30 n :=
  (((parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap :
      ParityPair n →L[ℂ] SectorSquare n).comp
    (T.comp ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap :
      SectorSquare n →L[ℂ] ParityPair n)))

def actualSchurTransposeAfterCoordinateV5_30 (n : ℤ)
    (T : ActualSchurPairEndomorphismV5_30 n) :
    ActualSchurPairEndomorphismV5_30 n :=
  ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap :
      SectorSquare n →L[ℂ] ParityPair n).comp
    ((actualCoordinateTranspose23 n
      (actualSchurEndomorphismToSquareV5_30 n T)).comp
      ((parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap :
        ParityPair n →L[ℂ] SectorSquare n))

theorem actualSchurTransposeAfterCoordinateV5_30_eq_actualPairTranspose
    (n : ℤ) (T : ActualSchurPairEndomorphismV5_30 n) :
    actualSchurTransposeAfterCoordinateV5_30 n T =
      actualPairTransposeAfterCoordinate23 n T := rfl

private abbrev actualTauJointV5_30 {n : ℤ}
    (T : ParityPair n →L[ℂ] ParityPair n) :=
  actualPairTransposeAfterCoordinate23 n T

private theorem actualTauJointV5_30_one (n : ℤ) :
    actualTauJointV5_30 (1 : ParityPair n →L[ℂ] ParityPair n) = 1 :=
  actualPairTransposeAfterCoordinate23_one_identityMinimumV1_30 n

def actualComplementaryQVDJointInverseV5_30 (n : ℤ)
    (x : ℂ × ActualH1PairJointSchurV5_30) : ParityPair n →L[ℂ] ParityPair n :=
  Ring.inverse (1 - actualComplementaryQVDJointParameterV5_30 n x)

private theorem actualJointQVDMatchesProofIndexedV5_30
    (n : ℤ) (z : ℂ) (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) :
    actualComplementaryQVDJointParameterV5_30 n (z, p) =
      freeResolventComplementaryPotentialOppositeFactor22
        (physicalH1ComplexCarrierToL2Actual22 p.1)
        (physicalH1ComplexCarrierToL2Actual22 p.2)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2)
        n z hz := by
  dsimp [actualComplementaryQVDJointParameterV5_30,
    freeResolventComplementaryPotentialOppositeFactor22]
  rw [actualFreeResolventCenterExtension_eq_actualV1_30 n z hz]
  rw [actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply]

/-- The total V5 inverse family has the exact proof-indexed complementary
resolvent formula on the signed spectral disk and the independent H¹ pair. -/
theorem actualComplementaryQVDJointInverse_eq_proofIndexedFormulaV5_30
    (n : ℤ) (z : ℂ) (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) :
    actualComplementaryQVDJointInverseV5_30 n (z, p) =
      Ring.inverse (1 - freeResolventComplementaryPotentialOppositeFactor22
        (physicalH1ComplexCarrierToL2Actual22 p.1)
        (physicalH1ComplexCarrierToL2Actual22 p.2)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)
        (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2)
        n z hz) := by
  change Ring.inverse (1 - actualComplementaryQVDJointParameterV5_30 n (z, p)) =
    Ring.inverse (1 - freeResolventComplementaryPotentialOppositeFactor22
      (physicalH1ComplexCarrierToL2Actual22 p.1)
      (physicalH1ComplexCarrierToL2Actual22 p.2)
      (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)
      (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2)
      n z hz)
  rw [actualJointQVDMatchesProofIndexedV5_30 n z p hz]

/-- The actual joint factor is a unit on the unchanged spectral disk and two
independent H¹ balls, by the actual squared-factor estimate. -/
theorem actualComplementaryQVDJointOneSubIsUnitV5_30
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    IsUnit (1 - actualComplementaryQVDJointParameterV5_30 n (z, p)) := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  have hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₁
  have hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₂
  have hsq := freeResolventComplementaryPotentialOpposite_square_norm_le_half_actual22
    u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz hlarge
  have hfactor : actualComplementaryQVDJointParameterV5_30 n (z, p) =
      freeResolventComplementaryPotentialOppositeFactor22
        u₁ u₂ hu₁ hu₂ n z hz := by
    simpa only [u₁, u₂, hu₁, hu₂] using
      actualJointQVDMatchesProofIndexedV5_30 n z p hz
  have hsmall :
      ‖actualComplementaryQVDJointParameterV5_30 n (z, p) *
        actualComplementaryQVDJointParameterV5_30 n (z, p)‖ < 1 := by
    rw [hfactor]
    linarith
  exact continuousLinearMap_one_sub_isUnit_of_square_norm_lt_one23
    (actualComplementaryQVDJointParameterV5_30 n (z, p)) hsmall

/-- The actual total inverse supplies both inverse equations for the actual
joint factor at each point of its concrete domain. -/
theorem actualComplementaryQVDJointInverseV5_30_twoSided
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    (actualComplementaryQVDJointInverseV5_30 n (z, p)).comp
        (1 - actualComplementaryQVDJointParameterV5_30 n (z, p)) = 1 ∧
      (1 - actualComplementaryQVDJointParameterV5_30 n (z, p)).comp
        (actualComplementaryQVDJointInverseV5_30 n (z, p)) = 1 := by
  let T : ParityPair n →L[ℂ] ParityPair n :=
    1 - actualComplementaryQVDJointParameterV5_30 n (z, p)
  have hunit := actualComplementaryQVDJointOneSubIsUnitV5_30
    R hR n hn hlarge z p hz hp₁ hp₂
  constructor
  · change Ring.inverse T * T = 1
    exact Ring.inverse_mul_cancel T hunit
  · change T * Ring.inverse T = 1
    exact Ring.mul_inverse_cancel T hunit

/-- The norm-convergent Neumann inverse from the actual opposite-factor
estimate is the same total inverse used by the joint family. -/
theorem actualComplementaryQVDJointInverse_eq_neumannV5_30
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ∃ N : ParityPair n →L[ℂ] ParityPair n,
      N = actualComplementaryQVDJointInverseV5_30 n (z, p) ∧
      N * (1 - actualComplementaryQVDJointParameterV5_30 n (z, p)) = 1 ∧
      (1 - actualComplementaryQVDJointParameterV5_30 n (z, p)) * N = 1 ∧
      ‖N‖ ≤ freeResolventComplementaryInverseUniformConstant22 * R := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  have hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₁
  have hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₂
  obtain ⟨N, hNleft, hNright, _, _, _, _, hNnorm⟩ :=
    freeResolventComplementaryPotentialOpposite_neumann_inverse_range_actual22
      u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz hlarge
  have hfactor : actualComplementaryQVDJointParameterV5_30 n (z, p) =
      freeResolventComplementaryPotentialOppositeFactor22
        u₁ u₂ hu₁ hu₂ n z hz := by
    simpa only [u₁, u₂, hu₁, hu₂] using
      actualJointQVDMatchesProofIndexedV5_30 n z p hz
  have hN : N = Ring.inverse
      (1 - freeResolventComplementaryPotentialOppositeFactor22
        u₁ u₂ hu₁ hu₂ n z hz) :=
    monoid_twoSidedInverse_unique_actual22 _ N _
      (by simpa only [ContinuousLinearMap.mul_def] using hNleft)
      (by
        simpa only [ContinuousLinearMap.mul_def] using
          Ring.mul_inverse_cancel
            (1 - freeResolventComplementaryPotentialOppositeFactor22
              u₁ u₂ hu₁ hu₂ n z hz)
            (by
              rw [← hfactor]
              exact actualComplementaryQVDJointOneSubIsUnitV5_30
                R hR n hn hlarge z p hz hp₁ hp₂))
  refine ⟨N, ?_, ?_, ?_, hNnorm⟩
  · dsimp [actualComplementaryQVDJointInverseV5_30]
    rw [hfactor, hN]
  · simpa only [hfactor] using hNleft
  · simpa only [hfactor] using hNright

/-- The true transpose fixes the concrete complementary resolvent built from
the actual proof-indexed D, independent-field V, and actual total inverse. -/
theorem actualSchurResolvent_transpose_fixed_jointV5_30
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
    let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
    let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
    let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
    actualPairTransposeAfterCoordinate23 n
      ((freeResolventParityPair n z hz).comp
        (Ring.inverse (1 - freeResolventComplementaryPotentialOppositeFactor22
          u₁ u₂ hu₁ hu₂ n z hz))) =
      (freeResolventParityPair n z hz).comp
        (Ring.inverse (1 - freeResolventComplementaryPotentialOppositeFactor22
          u₁ u₂ hu₁ hu₂ n z hz)) := by
  dsimp
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let V : ParityPair n →L[ℂ] ParityPair n := coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let Q : ParityPair n →L[ℂ] ParityPair n := freeResolventComplementaryProjectionTransported n
  let X : ParityPair n →L[ℂ] ParityPair n := 1 - D.comp (V.comp Q)
  let Y : ParityPair n →L[ℂ] ParityPair n := 1 - Q.comp (V.comp D)
  let S : ParityPair n →L[ℂ] ParityPair n := Ring.inverse Y
  have hunit : IsUnit Y := by
    have hA := actualComplementaryQVDJointOneSubIsUnitV5_30
      R hR n hn hlarge z p hz hp₁ hp₂
    have hfactor :
        actualComplementaryQVDJointParameterV5_30 n (z, p) =
          freeResolventComplementaryPotentialOppositeFactor22
            u₁ u₂ hu₁ hu₂ n z hz :=
      actualJointQVDMatchesProofIndexedV5_30 n z p hz
    have hF : IsUnit
        (1 - freeResolventComplementaryPotentialOppositeFactor22
          u₁ u₂ hu₁ hu₂ n z hz) := by
      rw [← hfactor]
      exact hA
    simpa only [Y, Q, V, D, freeResolventComplementaryPotentialOppositeFactor22] using hF
  have hSleft : S.comp Y = 1 := by
    change Ring.inverse Y * Y = 1
    exact Ring.inverse_mul_cancel Y hunit
  have hSright : Y.comp S = 1 := by
    change Y * Ring.inverse Y = 1
    exact Ring.mul_inverse_cancel Y hunit
  have hD : actualTauJointV5_30 D = D :=
    actualPairTranspose_freeResolvent_v6_24 n z hz
  have hV : actualTauJointV5_30 V = V :=
    actualPairTranspose_coveredPotential_v6_24 u₁ u₂ hu₁ hu₂ n
  have hQ : actualTauJointV5_30 Q = Q :=
    actualPairTranspose_complementary_v6_24 n
  have hD' : actualPairTransposeAfterCoordinate23 n D = D := hD
  have hV' : actualPairTransposeAfterCoordinate23 n V = V := hV
  have hQ' : actualPairTransposeAfterCoordinate23 n Q = Q := hQ
  have hY : actualTauJointV5_30 Y = X := by
    change actualPairTransposeAfterCoordinate23 n
        ((1 : ParityPair n →L[ℂ] ParityPair n) - Q.comp (V.comp D)) =
      (1 : ParityPair n →L[ℂ] ParityPair n) - D.comp (V.comp Q)
    calc
      _ = actualPairTransposeAfterCoordinate23 n (1 : ParityPair n →L[ℂ] ParityPair n) -
          actualPairTransposeAfterCoordinate23 n (Q.comp (V.comp D)) :=
        actualPairTransposeAfterCoordinate23_sub_prerequisiteV2_25 n _ _
      _ = 1 - (actualPairTransposeAfterCoordinate23 n D).comp
            ((actualPairTransposeAfterCoordinate23 n V).comp
              (actualPairTransposeAfterCoordinate23 n Q)) := by
        rw [actualPairTransposeAfterCoordinate23_one_identityMinimumV1_30,
          actualPairTransposeAfterCoordinate23_comp,
          actualPairTransposeAfterCoordinate23_comp]
        rw [← ContinuousLinearMap.comp_assoc]
      _ = 1 - D.comp (V.comp Q) := by
        rw [hD', hV', hQ']
  have hQD : Q.comp D = D :=
    freeResolventParityPair_comp_complementaryProjection_afterCoordinateRange n z hz
  have hDQ : D.comp Q = D :=
    freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange n z hz
  have hXY : X.comp D = D.comp Y := by
    exact freeResolventSchurFactors_intertwine_afterMonoid_actual22 D V Q hQD hDQ
  have hτSleft : (actualTauJointV5_30 S).comp X = 1 := by
    have h := congrArg (actualPairTransposeAfterCoordinate23 n) hSright
    simpa only [actualTauJointV5_30, actualPairTransposeAfterCoordinate23_comp,
      hY, actualTauJointV5_30_one] using h
  have hτSright : X.comp (actualTauJointV5_30 S) = 1 := by
    have h := congrArg (actualPairTransposeAfterCoordinate23 n) hSleft
    simpa only [actualTauJointV5_30, actualPairTransposeAfterCoordinate23_comp,
      hY, actualTauJointV5_30_one] using h
  have hshift : (actualTauJointV5_30 S).comp D = D.comp S := by
    have h := monoid_intertwining_twoSidedInverses_actual22
      X Y D (actualTauJointV5_30 S) S
      (by simpa only [ContinuousLinearMap.mul_def] using hXY)
      (by simpa only [ContinuousLinearMap.mul_def] using hτSleft)
      (by simpa only [ContinuousLinearMap.mul_def] using hSright)
    simpa only [ContinuousLinearMap.mul_def] using h
  have hRop : actualTauJointV5_30 (D.comp S) = D.comp S := by
    calc
      actualTauJointV5_30 (D.comp S) =
          (actualTauJointV5_30 S).comp (actualTauJointV5_30 D) :=
        actualPairTransposeAfterCoordinate23_comp n D S
      _ = (actualTauJointV5_30 S).comp D := by rw [hD]
      _ = D.comp S := hshift
  exact hRop

/-- The source Schur operator has equal concrete resonant diagonal entries on
the same joint domain. This follows from its actual flip transpose identity. -/
theorem actualSchurEffective_equal_diagonal_jointV5_30
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
    let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
    let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
    let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
      physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
    let P := resonantParityPair n
    let V := coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
    let S := Ring.inverse (1 - freeResolventComplementaryPotentialOppositeFactor22
      u₁ u₂ hu₁ hu₂ n z hz)
    let D := freeResolventParityPair n z hz
    let Rop := D.comp S
    let M := P.comp (V.comp P) + P.comp (V.comp (Rop.comp (V.comp P)))
    inner ℂ (parityPairVector n (true, resonantIndex n))
        (M (parityPairVector n (true, resonantIndex n))) =
      inner ℂ (parityPairVector n (false, resonantIndex n))
        (M (parityPairVector n (false, resonantIndex n))) := by
  dsimp
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  let V : ParityPair n →L[ℂ] ParityPair n := coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let Q : ParityPair n →L[ℂ] ParityPair n := freeResolventComplementaryProjectionTransported n
  let S : ParityPair n →L[ℂ] ParityPair n :=
    Ring.inverse (1 - freeResolventComplementaryPotentialOppositeFactor22
      u₁ u₂ hu₁ hu₂ n z hz)
  let Rop : ParityPair n →L[ℂ] ParityPair n := D.comp S
  let M : ParityPair n →L[ℂ] ParityPair n :=
    P.comp (V.comp P) + P.comp (V.comp (Rop.comp (V.comp P)))
  have hP : actualTauJointV5_30 P = P :=
    actualPairTranspose_resonant_v6_24 n
  have hV : actualTauJointV5_30 V = V :=
    actualPairTranspose_coveredPotential_v6_24 u₁ u₂ hu₁ hu₂ n
  have hR : actualTauJointV5_30 Rop = Rop := by
    exact actualSchurResolvent_transpose_fixed_jointV5_30
      R hR n hn hlarge z p hz hp₁ hp₂
  have hM : actualTauJointV5_30 M = M := by
    dsimp [M]
    simp only [actualPairTransposeAfterCoordinate23_add_prerequisiteV2_25,
      actualPairTransposeAfterCoordinate23_comp, hP, hV, hR,
      ContinuousLinearMap.comp_assoc]
  have hM' : actualPairTransposeAfterCoordinate23 n M = M := by
    simpa only [actualTauJointV5_30] using hM
  have hentry := actualPairTranspose24_single_matrix_entry_v2 n M
    (true, resonantIndex n) (true, resonantIndex n)
  rw [hM'] at hentry
  exact hentry

end NlsGge.Schur

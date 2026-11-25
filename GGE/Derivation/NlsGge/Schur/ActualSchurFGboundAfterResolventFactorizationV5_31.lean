import NlsGge.Schur.ActualComplementaryQVDJointInverseAndEqualDiagonalV5_30
import NlsGge.Schur.FreeResolventUniformBoundsPackageAfterScalarSqrtPrerequisite
import NlsGge.Schur.ComplementaryResolventCanonicalFormulaAfterMonoidPrerequisite
import NlsGge.Schur.ActualSchurGreenRepresentationBridgeV3_31
import NlsGge.Schur.ActualSchurDiagonalNormPrerequisitesV2_31

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- The actual complementary resolvent in the paper's formula
`D (1 - Q V D)⁻¹`, on the original signed spectral disk and independent
complex H¹ pair. -/
def actualSchurResolventFactorizedV5_31 (n : ℤ) (z : ℂ)
    (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) : ParityPair n →L[ℂ] ParityPair n := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n
  exact D.comp (actualComplementaryQVDJointInverseV5_30 n (z, p))

/-- The concrete `G_n = R_n V P` block from F:eq:FG. -/
def actualSchurGreenColumnV5_31 (n : ℤ) (z : ℂ)
    (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) : ParityPair n →L[ℂ] ParityPair n := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  exact (actualSchurResolventFactorizedV5_31 n z p hz).comp
    ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp (resonantParityPair n))

/-- The concrete `\widetilde G_n = P V R_n` block from F:eq:FG. -/
def actualSchurGreenRowV5_31 (n : ℤ) (z : ℂ)
    (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) : ParityPair n →L[ℂ] ParityPair n := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  exact (resonantParityPair n).comp
    ((coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n).comp
      (actualSchurResolventFactorizedV5_31 n z p hz))

/-- Actual F:eq:FGbound for the left Green block. The source-order
`D (1-QVD)⁻¹ V P` is transported through the proved intertwining identity to
`(1-DVQ)⁻¹ D V P`; the latter uses the actual free-resolvent column estimate
and actual complementary inverse norm. -/
theorem actualSchurGreenColumn_boundV5_31
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ‖actualSchurGreenColumnV5_31 n z p hz‖ ≤
      freeResolventComplementaryInverseUniformConstant22 *
        freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)| := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  let A : ParityPair n →L[ℂ] ParityPair n := D.comp (V.comp Q)
  let B : ParityPair n →L[ℂ] ParityPair n := Q.comp (V.comp D)
  let C : ParityPair n →L[ℂ] ParityPair n := D.comp (V.comp P)
  let Sleft : ParityPair n →L[ℂ] ParityPair n := Ring.inverse (1 - A)
  let Sright : ParityPair n →L[ℂ] ParityPair n := Ring.inverse (1 - B)
  have hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₁
  have hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₂
  obtain ⟨S₀, hS₀left, hS₀right, _, _, _, _, hS₀norm⟩ :=
    freeResolventComplementaryPotentialA_neumann_inverse_range_actual22
      u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz hlarge
  have hunit : IsUnit (1 - A) := by
    have hsquare := freeResolventComplementaryPotentialA_square_norm_le_half
      u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz hlarge
    exact continuousLinearMap_one_sub_isUnit_of_square_norm_lt_one23 A
      (lt_of_le_of_lt hsquare (by norm_num))
  have hleft : Sleft.comp (1 - A) = 1 := by
    simpa only [Sleft, ContinuousLinearMap.mul_def] using
      Ring.inverse_mul_cancel (1 - A) hunit
  have hright : (1 - A).comp Sleft = 1 := by
    simpa only [Sleft, ContinuousLinearMap.mul_def] using
      Ring.mul_inverse_cancel (1 - A) hunit
  have h₀left : S₀.comp (1 - A) = 1 := by
    simpa only [ContinuousLinearMap.mul_def, A, D, V, Q,
      freeResolventComplementaryPotentialA] using hS₀left
  have h₀right : (1 - A).comp S₀ = 1 := by
    simpa only [ContinuousLinearMap.mul_def, A, D, V, Q,
      freeResolventComplementaryPotentialA] using hS₀right
  have hSleft : ‖Sleft‖ ≤
      freeResolventComplementaryInverseUniformConstant22 * R := by
    have huniq := monoid_twoSidedInverse_unique_actual22 (1 - A) Sleft S₀
      (by simpa only [ContinuousLinearMap.mul_def] using hleft)
      (by simpa only [ContinuousLinearMap.mul_def] using h₀right)
    rw [huniq]
    exact hS₀norm
  have hunitRight : IsUnit (1 - B) := by
    have hsquare := freeResolventComplementaryPotentialOpposite_square_norm_le_half_actual22
      u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz hlarge
    exact continuousLinearMap_one_sub_isUnit_of_square_norm_lt_one23 B
      (lt_of_le_of_lt hsquare (by norm_num))
  have hSrightLeft : Sright.comp (1 - B) = 1 := by
    simpa only [Sright, ContinuousLinearMap.mul_def] using
      Ring.inverse_mul_cancel (1 - B) hunitRight
  have hSrightRight : (1 - B).comp Sright = 1 := by
    simpa only [Sright, ContinuousLinearMap.mul_def] using
      Ring.mul_inverse_cancel (1 - B) hunitRight
  have hQD : Q.comp D = D :=
    freeResolventParityPair_comp_complementaryProjection_afterCoordinateRange n z hz
  have hDQ : D.comp Q = D :=
    freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange n z hz
  have hcanonical := freeResolventSchurCanonicalFormula_afterMonoid_actual22
    D V Q Sleft Sleft Sright Sright hQD hDQ
    hleft hright hleft hright hSrightLeft hSrightRight hSrightLeft hSrightRight
  have hshift : Sleft.comp D = D.comp Sright := hcanonical.1
  have hInv : actualComplementaryQVDJointInverseV5_30 n (z, p) = Sright := by
    have hformula := actualComplementaryQVDJointInverse_eq_proofIndexedFormulaV5_30
      n z p hz
    simpa only [Sright, B, Q, V, D, u₁, u₂, hu₁, hu₂,
      freeResolventComplementaryPotentialOppositeFactor22] using! hformula
  have hcolumn : ‖C‖ ≤ freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
    have hpack := freeResolventPotential_uniform_bounds_on_h1_ball
      u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz
    have hsum : ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
        ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
        freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
      change _ ≤ freeResolventSchurUniformConstant * R / |(n : ℝ)|
      exact hpack.1
    have hle : ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ ≤
        ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
          ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ :=
      le_add_of_nonneg_right
        (norm_nonneg
          (resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz))
    change ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ ≤ _
    exact le_trans hle hsum
  have hRnonneg : 0 ≤ R := le_trans (by norm_num) hR
  have hnpos : 0 < |(n : ℝ)| := lt_of_lt_of_le (by norm_num) hn
  have hInvCpos : 0 < freeResolventComplementaryInverseUniformConstant22 :=
    freeResolventComplementaryInverseUniformConstant22_posV2_31
  have hInvCnonneg : 0 ≤ freeResolventComplementaryInverseUniformConstant22 :=
    le_of_lt hInvCpos
  have hSchurCnonneg : 0 ≤ freeResolventSchurUniformConstant := by
    unfold freeResolventSchurUniformConstant
    positivity
  have hSchurCpos : 0 < freeResolventSchurUniformConstant := by
    unfold freeResolventSchurUniformConstant
    positivity
  have hrepr : actualSchurGreenColumnV5_31 n z p hz = Sleft.comp C := by
    dsimp [actualSchurGreenColumnV5_31, actualSchurResolventFactorizedV5_31,
      C, D, V, P, u₁, u₂, hu₁, hu₂]
    exact actualSchurGreenColumn_representationBridgeV3_31
      n z p hz Sleft Sright hInv hshift
  calc
    ‖actualSchurGreenColumnV5_31 n z p hz‖ = ‖Sleft.comp C‖ := by rw [hrepr]
    _ ≤ ‖Sleft‖ * ‖C‖ := Sleft.opNorm_comp_le C
    _ ≤ (freeResolventComplementaryInverseUniformConstant22 * R) *
          (freeResolventSchurUniformConstant * R / |(n : ℝ)|) := by
      gcongr <;> positivity
    _ = freeResolventComplementaryInverseUniformConstant22 *
          freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)| := by ring

/-- The actual right Green block is bounded by the proved `P V D` row
estimate times the actual `Q V D` inverse norm. -/
theorem actualSchurGreenRow_boundV5_31
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualH1PairJointSchurV5_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ‖actualSchurGreenRowV5_31 n z p hz‖ ≤
      freeResolventComplementaryInverseUniformConstant22 *
        freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)| := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let Sright : ParityPair n →L[ℂ] ParityPair n :=
    Ring.inverse (1 - freeResolventComplementaryPotentialOppositeFactor22
      u₁ u₂ hu₁ hu₂ n z hz)
  have hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₁
  have hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₂
  obtain ⟨N, hN, _, _, hNnorm⟩ :=
    actualComplementaryQVDJointInverse_eq_neumannV5_30
      R hR n hn hlarge z p hz hp₁ hp₂
  have hS : N = Sright := by
    rw [hN, actualComplementaryQVDJointInverse_eq_proofIndexedFormulaV5_30 n z p hz]
  have hSnorm : ‖Sright‖ ≤ freeResolventComplementaryInverseUniformConstant22 * R := by
    rw [← hS]
    exact hNnorm
  have hSActual : actualComplementaryQVDJointInverseV5_30 n (z, p) = Sright :=
    hN.symm.trans hS
  have hrow : ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
    have hpack := freeResolventPotential_uniform_bounds_on_h1_ball
      u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz
    have hsum : ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
        ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
        freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
      change _ ≤ freeResolventSchurUniformConstant * R / |(n : ℝ)|
      exact hpack.1
    have hle : ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
        ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
          ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ :=
      le_add_of_nonneg_left
        (norm_nonneg
          (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz))
    exact le_trans hle hsum
  have hRnonneg : 0 ≤ R := le_trans (by norm_num) hR
  have hnpos : 0 < |(n : ℝ)| := lt_of_lt_of_le (by norm_num) hn
  have hSchurCnonneg : 0 ≤ freeResolventSchurUniformConstant := by
    unfold freeResolventSchurUniformConstant
    positivity
  have hrowEq : actualSchurGreenRowV5_31 n z p hz =
      (resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz).comp Sright := by
    dsimp [actualSchurGreenRowV5_31, actualSchurResolventFactorizedV5_31,
      u₁, u₂, hu₁, hu₂]
    exact actualSchurGreenRow_representationBridgeV3_31
      n z p hz Sright hSActual
  calc
    ‖actualSchurGreenRowV5_31 n z p hz‖ =
        ‖(resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz).comp Sright‖ := by
          rw [hrowEq]
    _ ≤ ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ * ‖Sright‖ :=
      (resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz).opNorm_comp_le Sright
    _ ≤ (freeResolventSchurUniformConstant * R / |(n : ℝ)|) *
          (freeResolventComplementaryInverseUniformConstant22 * R) := by
      have hrowFactor_nonneg :
          0 ≤ freeResolventSchurUniformConstant * R / |(n : ℝ)| :=
        div_nonneg (mul_nonneg hSchurCnonneg hRnonneg) (le_of_lt hnpos)
      calc
        _ ≤ (freeResolventSchurUniformConstant * R / |(n : ℝ)|) * ‖Sright‖ :=
          mul_le_mul_of_nonneg_right hrow (norm_nonneg Sright)
        _ ≤ (freeResolventSchurUniformConstant * R / |(n : ℝ)|) *
              (freeResolventComplementaryInverseUniformConstant22 * R) :=
          mul_le_mul_of_nonneg_left hSnorm hrowFactor_nonneg
    _ = freeResolventComplementaryInverseUniformConstant22 *
          freeResolventSchurUniformConstant * R ^ 2 / |(n : ℝ)| := by ring

end NlsGge.Schur

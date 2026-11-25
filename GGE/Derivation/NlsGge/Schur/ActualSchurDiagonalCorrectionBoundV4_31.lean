import NlsGge.Schur.ActualComplementaryQVDJointInverseAndEqualDiagonalV5_30
import NlsGge.Schur.ActualSchurEffectiveJointAnalyticAfterDextV3_30
import NlsGge.Schur.FreeResolventUniformBoundsPackageAfterScalarSqrtPrerequisite
import NlsGge.Schur.CoveredH1ParityPairPotentialNorm
import NlsGge.Schur.FreeResolventRankTwoProjectionPrerequisites
import NlsGge.Schur.ActualSchurDiagonalNormPrerequisitesV2_31

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- The concrete diagonal Schur correction `P V D S V P`, written in the
proof-indexed actual D presentation. On the spectral disk, batch-30's checked
Dext equality identifies this factor with the correction in its analytic
Dext-defined Schur operator. -/
def actualSchurDiagonalCorrectionV4_31 (n : ℤ) (z : ℂ)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hz : z ∈ spectralDisk n) : ParityPair n →L[ℂ] ParityPair n := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n
  let S : ParityPair n →L[ℂ] ParityPair n :=
    Ring.inverse (1 - Q.comp (V.comp D))
  exact (P.comp (V.comp D)).comp (S.comp (V.comp P))

/-- The actual correction entry has the source `C R^3/|n|` scale, with all
H¹, signed-index, and spectral-disk hypotheses explicit. The scalar constant
is displayed as the product of the already checked actual row, inverse, and
potential constants. -/
theorem actualSchurDiagonalCorrectionEntry_boundV4_31
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualSchurEffectiveH1PairV3_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ‖inner ℂ (parityPairVector n (true, resonantIndex n))
      (actualSchurDiagonalCorrectionV4_31 n z p hz
        (parityPairVector n (true, resonantIndex n)))‖ ≤
      2 * freeResolventSchurUniformConstant *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant * R ^ 3 / |(n : ℝ)| := by
  let u₁ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.1
  let u₂ : PhysicalL2 := physicalH1ComplexCarrierToL2Actual22 p.2
  let hu₁ : SobolevSquareSummable 1 (physicalFourier u₁) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1
  let hu₂ : SobolevSquareSummable 1 (physicalFourier u₂) :=
    physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2
  let P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n
  let V : ParityPair n →L[ℂ] ParityPair n :=
    coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
  let D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz
  let Q : ParityPair n →L[ℂ] ParityPair n :=
    freeResolventComplementaryProjectionTransported n
  let S : ParityPair n →L[ℂ] ParityPair n :=
    Ring.inverse (1 - Q.comp (V.comp D))
  let row : ParityPair n →L[ℂ] ParityPair n := P.comp (V.comp D)
  let e : ParityPair n := parityPairVector n (true, resonantIndex n)
  have hball₁ : ‖physicalSobolevL2 1 u₁ hu₁‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₁
  have hball₂ : ‖physicalSobolevL2 1 u₂ hu₂‖ ≤ R := by
    rw [actualPhysicalH1Carrier_sobolev_normAfterScalar23]
    exact hp₂
  have hrowPack := freeResolventPotential_uniform_bounds_on_h1_ball
    u₁ u₂ hu₁ hu₂ R hR hball₁ hball₂ n hn z hz
  have hrow : ‖row‖ ≤
      freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
    change ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤ _
    have hpack : ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
        ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
        freeResolventSchurUniformConstant * R / |(n : ℝ)| := by
      change _ ≤ freeResolventSchurUniformConstant * R / |(n : ℝ)|
      exact hrowPack.1
    have hle : ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ ≤
        ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz‖ +
          ‖resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz‖ :=
      le_add_of_nonneg_left
        (norm_nonneg (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz))
    exact le_trans hle hpack
  have hV : ‖V‖ ≤ 2 * physicalH1MultiplierConstant * R := by
    dsimp [V]
    exact coveredH1ParityPairPotential_norm_bound u₁ u₂ hu₁ hu₂ n R
      (le_trans (by norm_num) hR) hball₁ hball₂
  obtain ⟨N, hN, _, _, hNnorm⟩ :=
    actualComplementaryQVDJointInverse_eq_neumannV5_30
      R hR n hn hlarge z p hz hp₁ hp₂
  have hS : S = actualComplementaryQVDJointInverseV5_30 n (z, p) := by
    dsimp [S, Q, V, D, u₁, u₂, hu₁, hu₂]
    symm
    exact actualComplementaryQVDJointInverse_eq_proofIndexedFormulaV5_30
      n z p hz
  have hSnorm : ‖S‖ ≤ freeResolventComplementaryInverseUniformConstant22 * R := by
    rw [hS, ← hN]
    exact hNnorm
  have he_norm : ‖e‖ = 1 := by
    dsimp [e]
    rw [← (parityPairRepr n).norm_map, parityPairRepr_vector]
    simp
  have hPe : P e = e := by
    dsimp [P, e]
    simp [resonantParityPair_apply_basis]
  have hcorrection : actualSchurDiagonalCorrectionV4_31 n z p hz =
      row.comp (S.comp (V.comp P)) := by
    rfl
  have hTe : ‖actualSchurDiagonalCorrectionV4_31 n z p hz e‖ ≤
      ‖row‖ * (‖S‖ * (‖V‖ * ‖e‖)) := by
    rw [hcorrection]
    exact actualSchurDiagonalComposition_apply_norm_leV2_31 row S V P e hPe
  have hentry := parityPair_inner_norm_le_prerequisite n e
    (actualSchurDiagonalCorrectionV4_31 n z p hz e)
  have hCpos : 0 < freeResolventSchurUniformConstant := by
    unfold freeResolventSchurUniformConstant
    positivity
  have hIpos : 0 < freeResolventComplementaryInverseUniformConstant22 :=
    freeResolventComplementaryInverseUniformConstant22_posV2_31
  have hMpos : 0 < physicalH1MultiplierConstant :=
    physicalH1MultiplierConstant_pos
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hnpos : 0 < |(n : ℝ)| := lt_of_lt_of_le (by norm_num) hn
  have hTe' : ‖actualSchurDiagonalCorrectionV4_31 n z p hz e‖ ≤
      ‖row‖ * (‖S‖ * (‖V‖ * 1)) := by
    simpa only [he_norm] using hTe
  calc
    _ ≤ ‖e‖ * ‖actualSchurDiagonalCorrectionV4_31 n z p hz e‖ := hentry
    _ ≤ 1 * (‖row‖ * (‖S‖ * (‖V‖ * 1))) := by
      rw [he_norm]
      simpa only [one_mul] using hTe'
    _ ≤ 1 * ((freeResolventSchurUniformConstant * R / |(n : ℝ)|) *
        ((freeResolventComplementaryInverseUniformConstant22 * R) *
          ((2 * physicalH1MultiplierConstant * R) * 1))) := by
      gcongr <;> positivity
    _ = 2 * freeResolventSchurUniformConstant *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant * R ^ 3 / |(n : ℝ)| := by ring

end NlsGge.Schur

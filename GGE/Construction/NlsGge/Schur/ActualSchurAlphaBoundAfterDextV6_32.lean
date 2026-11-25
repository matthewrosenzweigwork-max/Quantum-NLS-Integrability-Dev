import NlsGge.Schur.ActualSchurCoefficientJointAnalyticV2_31
import NlsGge.Schur.ActualSchurDiagonalCorrectionBoundV4_31
import NlsGge.Schur.ActualComplementaryQVDJointInverseAndEqualDiagonalV5_30
import NlsGge.Schur.ActualPotentialTransposeEntryPrerequisites24
import NlsGge.Schur.FreeResolventPotentialMatrixEntriesAfterInnerScalar
import NlsGge.Schur.ResonantParityPairBasisAction
import NlsGge.Schur.ActualParityPairComplexInnerAddRightMinimumV1_32

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- On the actual signed spectral disk, the `++` diagonal coefficient of the
Dext-defined effective operator is exactly the concrete `P V D S V P`
correction entry. This identifies the analytic coefficient with the
proof-indexed actual correction: the Dext equality transports `D`, the V5
inverse equality transports `S`, and the same-channel actual potential entry
annuls `P V P`. -/
theorem actualSchurAlphaEqualsDiagonalCorrectionV6_32
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualSchurEffectiveH1PairV3_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    actualSchurCoefficientAfterDext31 n
      (true, resonantIndex n) (true, resonantIndex n) (z, p) =
    inner ℂ (parityPairVector n (true, resonantIndex n))
      (actualSchurDiagonalCorrectionV4_31 n z p hz
        (parityPairVector n (true, resonantIndex n))) := by
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
  let e : ParityPair n := parityPairVector n (true, resonantIndex n)
  have hD : actualFreeResolventCenterExtensionV1_30 n z = D :=
    actualFreeResolventCenterExtension_eq_actualV1_30 n z hz
  have hS : Ring.inverse
      (1 - actualComplementaryQVDJointParameterV5_30 n (z, p)) = S := by
    change actualComplementaryQVDJointInverseV5_30 n (z, p) = S
    exact actualComplementaryQVDJointInverse_eq_proofIndexedFormulaV5_30
      n z p hz
  have hV :
      actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p = V := by
    dsimp [V, u₁, u₂, hu₁, hu₂]
    exact actualParityPairPotentialParameterAfterScalarWrapperCLM23_apply n p
  have hM : actualSchurEffectiveOperatorAfterDextV3_30 n (z, p) =
      P.comp (V.comp P) +
        P.comp (V.comp ((D.comp S).comp (V.comp P))) := by
    dsimp [actualSchurEffectiveOperatorAfterDextV3_30]
    rw [hV, hD, hS]
  have hPe : P e = e := by
    dsimp [P, e]
    simp [resonantParityPair_apply_basis]
  have hProw (x : ParityPair n) : inner ℂ e (P x) = inner ℂ e x := by
    calc
      inner ℂ e (P x) = parityPairRepr n (P x) (true, resonantIndex n) := by
        exact (parityPairRepr_inner n (P x)
          (true, resonantIndex n)).symm
      _ = parityPairRepr n x (true, resonantIndex n) := by
        simp [P, resonantParityPair_repr_apply]
      _ = inner ℂ e x := parityPairRepr_inner n x (true, resonantIndex n)
  have hsame : inner ℂ e (V e) = 0 := by
    dsimp [e, V, u₁, u₂, hu₁, hu₂]
    exact actualPotentialTranspose_same_channel_entry_zero24
      (physicalH1ComplexCarrierToL2Actual22 p.1)
      (physicalH1ComplexCarrierToL2Actual22 p.2)
      (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.1)
      (physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable p.2)
      n true (resonantIndex n) (resonantIndex n)
  have hfirst : inner ℂ e (P.comp (V.comp P) e) = 0 := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hPe,
      hProw, hsame]
  have hcorrection :
      actualSchurDiagonalCorrectionV4_31 n z p hz =
        P.comp (V.comp ((D.comp S).comp (V.comp P))) := by
    dsimp [actualSchurDiagonalCorrectionV4_31, u₁, u₂, hu₁, hu₂,
      P, V, D, Q, S]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
  rw [actualSchurCoefficientAfterDext31]
  change inner ℂ e (actualSchurEffectiveOperatorAfterDextV3_30 n (z, p) e) = _
  rw [hM, ContinuousLinearMap.add_apply]
  have hinner :
      inner ℂ e ((P.comp (V.comp P)) e +
        (P.comp (V.comp ((D.comp S).comp (V.comp P)))) e) =
      inner ℂ e ((P.comp (V.comp P)) e) +
        inner ℂ e ((P.comp (V.comp ((D.comp S).comp (V.comp P)))) e) := by
    exact actualParityPairComplexInnerAddRightMinimumV1_32 n e _ _
  rw [hinner, hfirst, hcorrection]
  simpa only [zero_add, e]

/-- The actual Dext-defined diagonal Schur coefficient has the source
`C R^3/|n|` estimate, with the load-bearing correction bound discharged by
actual row, inverse, and potential estimates. -/
theorem actualSchurAlpha_boundAfterDextV6_32
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualSchurEffectiveH1PairV3_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    ‖actualSchurCoefficientAfterDext31 n
      (true, resonantIndex n) (true, resonantIndex n) (z, p)‖ ≤
      2 * freeResolventSchurUniformConstant *
        freeResolventComplementaryInverseUniformConstant22 *
        physicalH1MultiplierConstant * R ^ 3 / |(n : ℝ)| := by
  rw [actualSchurAlphaEqualsDiagonalCorrectionV6_32
    R hR n hn hlarge z p hz hp₁ hp₂]
  exact actualSchurDiagonalCorrectionEntry_boundV4_31
    R hR n hn hlarge z p hz hp₁ hp₂

end NlsGge.Schur

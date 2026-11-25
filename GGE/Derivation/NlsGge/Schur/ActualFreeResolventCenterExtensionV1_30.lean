import NlsGge.Schur.ActualCoordinateFreeResolventCenterInverseAnalyticPrerequisiteV1_26
import NlsGge.Schur.ActualCoordinatePairCenterFactorConjugacyV2_26
import NlsGge.Schur.ActualCoordinatePairCenterInverseConjugacyAfterUnitV3_26
import NlsGge.Schur.ActualFreeResolventCenterParityPairNormAfterSquareV2_24
import NlsGge.Schur.ActualFreeResolventParityPairCenterShiftIdentityV3_25
import NlsGge.Schur.GenericCenterFactorCLMScalarModulePrerequisiteV2_25
import NlsGge.Schur.ActualCoordinatePairConjugacyPostcomposeAnalyticV3_29
import NlsGge.Schur.ActualFreeResolventCenterDictionaryTransportMinimumV3_29
import NlsGge.Schur.ActualCoordinateFreeResolventCenterExtensionNamedFunctionModuleCoherenceMinimumV1_30
import Mathlib.Analysis.Analytic.Constructions

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The actual paired center value at the signed spectral center. -/
private def actualPairCenterD0V1_30 (n : ℤ) :
    ParityPair n →L[ℂ] ParityPair n :=
  freeResolventParityPair n (spectralCenter n)
    (spectralCenter_mem_spectralDisk_scalarV2_24 n)

/-- The paired total free-resolvent family, defined by conjugating the exact
named coordinate inverse-times-center family through the actual Fourier
isometry. -/
def actualFreeResolventCenterExtensionV1_30 (n : ℤ) (z : ℂ) :
    ParityPair n →L[ℂ] ParityPair n :=
  actualCoordinatePairEndomorphismConjugacyV2_26 n
    (actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30 n z)

/-- The actual named coordinate Dext family is analytic on the radius-two
neighborhood. Its inverse factor is the checked actual coordinate inverse;
its fixed multiplier is the actual signed-center free resolvent. -/
theorem actualCoordinateFreeResolventCenterExtension_analyticOnNhdV1_30
    (n : ℤ) :
    letI : NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n) :=
      ContinuousLinearMap.toNormedSpace
    AnalyticOnNhd ℂ
      (actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30 n)
      (Metric.ball (spectralCenter n) 2) := by
  letI : NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n) :=
    (CStarAlgebra.toNonUnitalCStarAlgebra
      (SectorSquare n →L[ℂ] SectorSquare n)).toNormedSpace
  have hinv := actualCoordinateFreeResolventCenterFactorInverse_analyticOnNhdV1_26 n
  have htotalCStar : AnalyticOnNhd ℂ
      (fun z : ℂ =>
        Ring.inverse
          (1 + (z - spectralCenter n) •
            actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) *
          actualCoordinateCenterD0NamedFunctionMinimumV1_30 n)
      (Metric.ball (spectralCenter n) 2) := by
    simpa only [actualCoordinateCenterD0NamedFunctionMinimumV1_30] using
      hinv.mul analyticOnNhd_const
  have hspace :
      (CStarAlgebra.toNonUnitalCStarAlgebra
        (SectorSquare n →L[ℂ] SectorSquare n)).toNormedSpace =
      (ContinuousLinearMap.toNormedSpace :
        NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n)) := by
    have hmodule :=
      (actualCoordinateEndomorphismNormedModule_eq_cstarV1_28 n).symm
    cases hmodule
    rfl
  have hprop :
      (letI : NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n) :=
        (CStarAlgebra.toNonUnitalCStarAlgebra
          (SectorSquare n →L[ℂ] SectorSquare n)).toNormedSpace;
        AnalyticOnNhd ℂ
          (fun z : ℂ =>
            Ring.inverse
              (1 + (z - spectralCenter n) •
                actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) *
              actualCoordinateCenterD0NamedFunctionMinimumV1_30 n)
          (Metric.ball (spectralCenter n) 2)) =
      (letI : NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n) :=
        ContinuousLinearMap.toNormedSpace;
        AnalyticOnNhd ℂ
          (fun z : ℂ =>
            Ring.inverse
              (1 + (z - spectralCenter n) •
                actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) *
              actualCoordinateCenterD0NamedFunctionMinimumV1_30 n)
          (Metric.ball (spectralCenter n) 2)) := by
    exact congrArg
      (fun ns : NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n) =>
        (letI : NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n) := ns;
        AnalyticOnNhd ℂ
          (fun z : ℂ =>
            Ring.inverse
              (1 + (z - spectralCenter n) •
                actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) *
              actualCoordinateCenterD0NamedFunctionMinimumV1_30 n)
          (Metric.ball (spectralCenter n) 2))) hspace
  have htotalOp := hprop.mp htotalCStar
  rw [actualCoordinateFreeResolventCenterExtension_functionModuleCoherenceMinimumV1_30 n]
    at htotalOp
  exact htotalOp

/-- The actual paired family is analytic on the same radius-two neighborhood,
by postcomposition with the checked actual Fourier-conjugacy CLM. -/
theorem actualFreeResolventCenterExtension_analyticOnNhdV1_30
    (n : ℤ) :
    letI : NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n) :=
      ContinuousLinearMap.toNormedSpace
    letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
      ContinuousLinearMap.toNormedSpace
    AnalyticOnNhd ℂ (actualFreeResolventCenterExtensionV1_30 n)
      (Metric.ball (spectralCenter n) 2) := by
  have hcoord := actualCoordinateFreeResolventCenterExtension_analyticOnNhdV1_30 n
  have hpost := actualCoordinatePairConjugacy_analyticOnNhdV3_29 n
    (Metric.ball (spectralCenter n) 2)
    (actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30 n) hcoord
  change AnalyticOnNhd ℂ
    (fun z => actualCoordinatePairEndomorphismConjugacyV2_26 n
      (actualCoordinateFreeResolventCenterExtensionNamedFunctionMinimumV1_30 n z))
    (Metric.ball (spectralCenter n) 2) at hpost
  exact hpost

private theorem actualCoordinatePair_centerD0_conjugacyV1_30 (n : ℤ) :
    actualCoordinatePairEndomorphismConjugacyV2_26 n
      (actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) =
    actualPairCenterD0V1_30 n := by
  rw [← actualCoordinatePairConjugacyCLM_eq_endomorphismConjugacy_pointwiseV1_28]
  ext x
  rw [actualCoordinatePairConjugacyContinuousLinearMap_applyV1_27]
  rfl

/-- On the complete actual signed spectral disk, the total paired family is
exactly the proof-indexed off-own-mode paired free resolvent. -/
theorem actualFreeResolventCenterExtension_eq_actualV1_30
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    actualFreeResolventCenterExtensionV1_30 n z =
      freeResolventParityPair n z hz := by
  letI : NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n) :=
    ContinuousLinearMap.toNormedSpace
  let S : ParityPair n →L[ℂ] ParityPair n :=
    1 + (z - spectralCenter n) • actualPairCenterD0V1_30 n
  have hdist : ‖z - spectralCenter n‖ ≤ 1 := by
    change ‖z - spectralCenter n‖ ≤ 1 at hz
    exact hz
  have hsmall :
      ‖(z - spectralCenter n) • actualPairCenterD0V1_30 n‖ < 1 := by
    calc
      ‖(z - spectralCenter n) • actualPairCenterD0V1_30 n‖ ≤
          ‖z - spectralCenter n‖ * ‖actualPairCenterD0V1_30 n‖ :=
        genericCenterFactor_norm_smul_clm_prerequisiteV2_25
          (z - spectralCenter n) (actualPairCenterD0V1_30 n)
      _ ≤ ‖z - spectralCenter n‖ * (1 / (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left
          (freeResolventParityPair_center_norm_le_afterSquareV2_24 n)
          (norm_nonneg _)
      _ ≤ 1 * (1 / (2 * Real.pi)) := by
        gcongr
      _ < 1 := by
        have hden : (1 : ℝ) < 2 * Real.pi := by
          nlinarith [Real.pi_gt_three]
        have hratio : (1 : ℝ) / (2 * Real.pi) < 1 :=
          (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).2 (by
            nlinarith [hden])
        simpa only [one_mul] using hratio
  have hunit : IsUnit S := by
    have h := IsUnit.one_sub_of_norm_lt_one
      (x := -((z - spectralCenter n) • actualPairCenterD0V1_30 n)) (by
        calc
          ‖-((z - spectralCenter n) • actualPairCenterD0V1_30 n)‖ =
              ‖(z - spectralCenter n) • actualPairCenterD0V1_30 n‖ :=
            actualPairEndomorphism_norm_negMinimumV3_29 n
              ((z - spectralCenter n) • actualPairCenterD0V1_30 n)
          _ < 1 := hsmall)
    have h' : IsUnit (1 - -((z - spectralCenter n) •
        actualPairCenterD0V1_30 n)) := h
    have h'' := actualPairEndomorphism_isUnit_one_add_of_sub_negMinimumV3_29 n
      ((z - spectralCenter n) • actualPairCenterD0V1_30 n) h'
    simpa only [S] using h''
  have hzball : z ∈ Metric.ball (spectralCenter n) 2 := by
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖z - spectralCenter n‖ < 2
    linarith
  have hinv := actualCoordinatePairCenterFactorInverse_conjugacyV3_26 n z hzball
  have hD0 := actualCoordinatePair_centerD0_conjugacyV1_30 n
  have hinv' :
      actualCoordinatePairEndomorphismConjugacyV2_26 n
          (Ring.inverse (1 + (z - spectralCenter n) •
            actualCoordinateCenterD0NamedFunctionMinimumV1_30 n)) =
        Ring.inverse S := by
    change actualCoordinatePairEndomorphismConjugacyV2_26 n
        (Ring.inverse (1 + (z - spectralCenter n) •
          freeResolventSquare n (spectralCenter n)
            (spectralCenter_mem_spectralDisk_scalarV2_24 n))) =
      Ring.inverse (1 + (z - spectralCenter n) •
        freeResolventParityPair n (spectralCenter n)
          (spectralCenter_mem_spectralDisk_scalarV2_24 n)) at hinv
    simpa only [actualCoordinateCenterD0NamedFunctionMinimumV1_30,
      actualPairCenterD0V1_30, S] using hinv
  have hpairedFormula :
      actualFreeResolventCenterExtensionV1_30 n z =
        Ring.inverse S * actualPairCenterD0V1_30 n := by
    change actualCoordinatePairEndomorphismConjugacyV2_26 n
      (Ring.inverse
        (1 + (z - spectralCenter n) •
          actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) *
        actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) = _
    calc
      _ = actualCoordinatePairEndomorphismConjugacyV2_26 n
          (Ring.inverse
            (1 + (z - spectralCenter n) •
              actualCoordinateCenterD0NamedFunctionMinimumV1_30 n)) *
          actualCoordinatePairEndomorphismConjugacyV2_26 n
            (actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) := map_mul _ _ _
      _ = Ring.inverse S * actualPairCenterD0V1_30 n := by
        rw [hD0, hinv']
  have hshift := freeResolventParityPair_center_shift_identity_v3_25 n z hz
  have hshift' : S * freeResolventParityPair n z hz = actualPairCenterD0V1_30 n := by
    simpa only [S, actualPairCenterD0V1_30] using hshift
  calc
    actualFreeResolventCenterExtensionV1_30 n z =
        Ring.inverse S * actualPairCenterD0V1_30 n := hpairedFormula
    _ = Ring.inverse S * (S * freeResolventParityPair n z hz) := by
      rw [← hshift']
    _ = (Ring.inverse S * S) * freeResolventParityPair n z hz := by
      rw [← mul_assoc]
    _ = freeResolventParityPair n z hz := by
      rw [Ring.inverse_mul_cancel S hunit, one_mul]

end NlsGge.Schur

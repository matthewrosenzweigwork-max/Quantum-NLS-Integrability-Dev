import NlsGge.Schur.FreeResolvent
import NlsGge.Schur.ActualFreeResolventCenterSquareNormAfterScalarV3_24
import NlsGge.Schur.ActualComplementarySchurUnitAndAnalyticInverse23
import NlsGge.Schur.GenericCenterFactorCLMScalarModulePrerequisiteV2_25
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Operator.Mul

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The analytic inverse of the actual center factor, first on its genuine
coordinate Hilbert carrier. -/
theorem actualCoordinateFreeResolventCenterFactorInverse_analyticOnNhdV1_26
    (n : ℤ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => Ring.inverse
        (1 + (z - spectralCenter n) •
          freeResolventSquare n (spectralCenter n)
            (spectralCenter_mem_spectralDisk_scalarV2_24 n)))
      (Metric.ball (spectralCenter n) 2) := by
  letI : NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n) :=
    ContinuousLinearMap.toNormedSpace
  let U : Set ℂ := Metric.ball (spectralCenter n) 2
  let D₀ : SectorSquare n →L[ℂ] SectorSquare n :=
    freeResolventSquare n (spectralCenter n)
      (spectralCenter_mem_spectralDisk_scalarV2_24 n)
  let A : ℂ → SectorSquare n →L[ℂ] SectorSquare n :=
    fun z => -((z - spectralCenter n) • D₀)
  have hdelta : AnalyticOnNhd ℂ (fun z : ℂ => z - spectralCenter n) U :=
    analyticOnNhd_id.sub analyticOnNhd_const
  have hA : AnalyticOnNhd ℂ A U := by
    simpa only [A, neg_smul] using
      (genericCenterFactor_analytic_smul_clm_prerequisiteV2_25
        U (fun z : ℂ => -(z - spectralCenter n)) hdelta.neg D₀)
  have hfactor : AnalyticOnNhd ℂ
      (fun z : ℂ => (1 : SectorSquare n →L[ℂ] SectorSquare n) - A z) U :=
    analyticOnNhd_const.sub hA
  have hAmap : Set.MapsTo A U
      {T : SectorSquare n →L[ℂ] SectorSquare n | ‖T * T‖ ≤ (1 / 2 : ℝ)} := by
    intro z hz
    have hzdist : ‖z - spectralCenter n‖ < 2 := by
      simpa only [U, Metric.mem_ball, dist_eq_norm] using hz
    have hD₀ := freeResolventSquare_center_norm_le_scalarV3_24 n
    have hnorm : ‖A z‖ < (1 / 3 : ℝ) := by
      calc
        ‖A z‖ = ‖(z - spectralCenter n) • D₀‖ := by
          simp [A, norm_neg]
        _ ≤ ‖z - spectralCenter n‖ * ‖D₀‖ :=
          genericCenterFactor_norm_smul_clm_prerequisiteV2_25
            (z - spectralCenter n) D₀
        _ ≤ ‖z - spectralCenter n‖ * (1 / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hD₀ (norm_nonneg _)
        _ < 2 * (1 / (2 * Real.pi)) :=
          mul_lt_mul_of_pos_right hzdist (by positivity)
        _ < (1 / 3 : ℝ) := by
          have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
          rw [show 2 * (1 / (2 * Real.pi)) = 1 / Real.pi by field_simp]
          exact (div_lt_iff₀ Real.pi_pos).2 (by linarith)
    have hproduct : ‖A z * A z‖ ≤ ‖A z‖ * ‖A z‖ := norm_mul_le _ _
    have hsq : ‖A z‖ * ‖A z‖ < (1 / 9 : ℝ) := by
      nlinarith [norm_nonneg (A z)]
    change ‖A z * A z‖ ≤ (1 / 2 : ℝ)
    linarith
  have hinv : AnalyticOnNhd ℂ
      (fun z : ℂ => Ring.inverse ((1 : SectorSquare n →L[ℂ] SectorSquare n) - A z)) U := by
    simpa only [Function.comp_def] using
      (analyticOnNhd_ringInverse_one_sub_of_square_le_half23
        (E := SectorSquare n)).comp hA hAmap
  simpa only [A, D₀, sub_neg_eq_add, U] using hinv

end NlsGge.Schur

import NlsGge.Schur.FreeResolventPotentialBlocks
import NlsGge.Schur.ActualCoordinatePairCenterFactorConjugacyV2_26
import NlsGge.Schur.ActualFreeResolventCenterSquareNormAfterScalarV3_24
import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

private def coordinateCenterFactorV3_26 (n : ℤ) (z : ℂ) :
    SectorSquare n →L[ℂ] SectorSquare n :=
  1 + (z - spectralCenter n) •
    freeResolventSquare n (spectralCenter n)
      (spectralCenter_mem_spectralDisk_scalarV2_24 n)

private def pairCenterFactorV3_26 (n : ℤ) (z : ℂ) :
    ParityPair n →L[ℂ] ParityPair n :=
  1 + (z - spectralCenter n) •
    freeResolventParityPair n (spectralCenter n)
      (spectralCenter_mem_spectralDisk_scalarV2_24 n)

private theorem coordinateCenterFactor_isUnitV3_26
    (n : ℤ) (z : ℂ) (hz : z ∈ Metric.ball (spectralCenter n) 2) :
    IsUnit (coordinateCenterFactorV3_26 n z) := by
  letI : NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n) :=
    ContinuousLinearMap.toNormedSpace
  let D₀ : SectorSquare n →L[ℂ] SectorSquare n :=
    freeResolventSquare n (spectralCenter n)
      (spectralCenter_mem_spectralDisk_scalarV2_24 n)
  have hzdist : ‖z - spectralCenter n‖ < 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hD₀ := freeResolventSquare_center_norm_le_scalarV3_24 n
  have hsmall : ‖(z - spectralCenter n) • D₀‖ < 1 := by
    calc
      ‖(z - spectralCenter n) • D₀‖ ≤
          ‖z - spectralCenter n‖ * ‖D₀‖ := by
            simpa only using!
              (norm_smul_le (z - spectralCenter n) D₀)
      _ ≤ ‖z - spectralCenter n‖ * (1 / (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hD₀ (norm_nonneg _)
      _ < 2 * (1 / (2 * Real.pi)) :=
        mul_lt_mul_of_pos_right hzdist (by positivity)
      _ < 1 := by
        have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
        rw [show 2 * (1 / (2 * Real.pi)) = 1 / Real.pi by field_simp]
        exact (div_lt_iff₀ Real.pi_pos).2 (by linarith)
  have h := IsUnit.one_sub_of_norm_lt_one
    (x := -((z - spectralCenter n) • D₀)) (by
      simpa only [norm_neg] using hsmall)
  simpa only [coordinateCenterFactorV3_26, D₀, sub_neg_eq_add] using h

/-- The totalized inverse transports on the actual radius-two ball. The
inverse equations follow from the mapped coordinate unit and actual factor
conjugacy. -/
theorem actualCoordinatePairCenterFactorInverse_conjugacyV3_26
    (n : ℤ) (z : ℂ) (hz : z ∈ Metric.ball (spectralCenter n) 2) :
    actualCoordinatePairEndomorphismConjugacyV2_26 n
        (Ring.inverse (coordinateCenterFactorV3_26 n z)) =
      Ring.inverse (pairCenterFactorV3_26 n z) := by
  let Φ := actualCoordinatePairEndomorphismConjugacyV2_26 n
  have hfactor := actualCoordinatePairCenterFactor_conjugacyV2_26 n z
  change Φ (coordinateCenterFactorV3_26 n z) = pairCenterFactorV3_26 n z at hfactor
  have hunitSq := coordinateCenterFactor_isUnitV3_26 n z hz
  have hunitPair : IsUnit (pairCenterFactorV3_26 n z) := by
    rw [← hfactor]
    exact hunitSq.map Φ.toRingHom
  have hmul : Φ (Ring.inverse (coordinateCenterFactorV3_26 n z)) *
      pairCenterFactorV3_26 n z = 1 := by
    calc
      Φ (Ring.inverse (coordinateCenterFactorV3_26 n z)) *
          pairCenterFactorV3_26 n z =
        Φ (Ring.inverse (coordinateCenterFactorV3_26 n z)) *
          Φ (coordinateCenterFactorV3_26 n z) := by rw [hfactor]
      _ = Φ (Ring.inverse (coordinateCenterFactorV3_26 n z) *
          coordinateCenterFactorV3_26 n z) := by rw [map_mul]
      _ = Φ 1 := by rw [Ring.inverse_mul_cancel _ hunitSq]
      _ = 1 := map_one Φ
  calc
    Φ (Ring.inverse (coordinateCenterFactorV3_26 n z)) =
        Φ (Ring.inverse (coordinateCenterFactorV3_26 n z)) * 1 := by rw [mul_one]
    _ = Φ (Ring.inverse (coordinateCenterFactorV3_26 n z)) *
        (pairCenterFactorV3_26 n z * Ring.inverse (pairCenterFactorV3_26 n z)) := by
          rw [← Ring.mul_inverse_cancel _ hunitPair]
    _ = (Φ (Ring.inverse (coordinateCenterFactorV3_26 n z)) *
        pairCenterFactorV3_26 n z) *
        Ring.inverse (pairCenterFactorV3_26 n z) := by rw [mul_assoc]
    _ = Ring.inverse (pairCenterFactorV3_26 n z) := by rw [hmul, one_mul]

end NlsGge.Schur

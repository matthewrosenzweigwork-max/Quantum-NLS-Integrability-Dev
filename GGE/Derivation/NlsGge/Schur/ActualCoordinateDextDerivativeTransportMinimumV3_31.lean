import NlsGge.Schur.ActualFreeResolventCenterExtensionV1_30

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Topology
open NlsGge.Analysis

namespace NlsGge.Schur

/-- The actual coordinate center factor is invertible on the complete
radius-two ball, including the signed zero mode. -/
theorem actualCoordinateCenterFactor_isUnit_radiusTwoMinimumV3_31
    (n : ℤ) (z : ℂ)
    (hz : z ∈ Metric.ball (spectralCenter n) 2) :
    IsUnit (1 + (z - spectralCenter n) •
      actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) := by
  let D₀ : SectorSquare n →L[ℂ] SectorSquare n :=
    actualCoordinateCenterD0NamedFunctionMinimumV1_30 n
  have hzdist : ‖z - spectralCenter n‖ < 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hD₀ := freeResolventSquare_center_norm_le_scalarV3_24 n
  have hsmall : ‖(z - spectralCenter n) • D₀‖ < 1 := by
    calc
      ‖(z - spectralCenter n) • D₀‖ ≤ ‖z - spectralCenter n‖ * ‖D₀‖ :=
        genericCenterFactor_norm_smul_clm_prerequisiteV2_25
          (z - spectralCenter n) D₀
      _ ≤ ‖z - spectralCenter n‖ * (1 / (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hD₀ (norm_nonneg _)
      _ < 2 * (1 / (2 * Real.pi)) :=
        mul_lt_mul_of_pos_right hzdist (by positivity)
      _ < 1 := by
        have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
        rw [show 2 * (1 / (2 * Real.pi)) = 1 / Real.pi by field_simp]
        exact (div_lt_iff₀ Real.pi_pos).2 (by linarith)
  have hunit := IsUnit.one_sub_of_norm_lt_one
    (x := -((z - spectralCenter n) • D₀)) (by
      simpa only [norm_neg] using hsmall)
  simpa only [D₀, sub_neg_eq_add] using hunit

/-- The actual inverse of an actual unit witness for the radius-two center
factor agrees with `Ring.inverse` at the concrete coordinate endomorphism
carrier. This isolates the unit-coercion normalization independently of the
derivative theorem. -/
theorem actualCoordinateCenterFactor_unitInverse_eq_ringInverseMinimumV3_31
    (n : ℤ) (z : ℂ)
    (hunit : IsUnit (1 + (z - spectralCenter n) •
      actualCoordinateCenterD0NamedFunctionMinimumV1_30 n)) :
    ((hunit.unit⁻¹ : (SectorSquare n →L[ℂ] SectorSquare n)ˣ) :
      SectorSquare n →L[ℂ] SectorSquare n) =
      Ring.inverse (1 + (z - spectralCenter n) •
        actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) := by
  have hu : (hunit.unit : SectorSquare n →L[ℂ] SectorSquare n) =
      1 + (z - spectralCenter n) •
        actualCoordinateCenterD0NamedFunctionMinimumV1_30 n := hunit.unit_spec
  calc
    ((hunit.unit⁻¹ : (SectorSquare n →L[ℂ] SectorSquare n)ˣ) :
        SectorSquare n →L[ℂ] SectorSquare n) =
        Ring.inverse (hunit.unit : SectorSquare n →L[ℂ] SectorSquare n) :=
      (Ring.inverse_unit hunit.unit).symm
    _ = Ring.inverse (1 + (z - spectralCenter n) •
        actualCoordinateCenterD0NamedFunctionMinimumV1_30 n) :=
      congrArg Ring.inverse hu

/-- The exact actual NormedSpace-module versus ambient CLM-module identity
used to transport coordinate inverse derivative maps to the named Dext target.
This re-exports the stored batch-30 dictionary minimum at the precise carrier. -/
theorem actualCoordinateDextDerivativeModuleDictionary_minimumV1_31
    (n : ℤ) :
    (ContinuousLinearMap.toNormedSpace :
      NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n)).toModule =
      ContinuousLinearMap.module :=
  actualCoordinateOperatorModule_eq_ambientModuleNamedFunctionMinimumV1_30 n

end NlsGge.Schur

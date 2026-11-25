import NlsGge.Spectral.ImaginaryResolventKernelAPIProbeV2

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot.ImaginaryResolventReciprocalFinalInequalityPrerequisiteV2

/-- The final rational step for the all-mode signed resolvent bound. -/
theorem reciprocal_final_inequality {y : ℝ} (hy : 1 ≤ y) :
    1 / y ^ 2 + 1 / y ≤ 2 / y := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hrecip : 1 / y ^ 2 ≤ 1 / y := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [sq_nonneg (y - 1)]
  calc
    1 / y ^ 2 + 1 / y ≤ 1 / y + 1 / y := add_le_add hrecip le_rfl
    _ = 2 / y := by ring

end NlsGge.Pilot.ImaginaryResolventReciprocalFinalInequalityPrerequisiteV2

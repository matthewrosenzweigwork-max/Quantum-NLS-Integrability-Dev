import NlsGge.Spectral.ActualNegativeVR0LargeImaginaryMinusTwoSidedInverseV1
import NlsGge.Spectral.ActualVR0LargeImaginaryMinusTwoSidedInverseV2

set_option autoImplicit false
noncomputable section
namespace NlsGge.Schur
open NlsGge.Pilot

/-- A single positive magnitude works simultaneously for both imaginary signs
and all parity indices, for every independent physical L² field pair.
This is the actual source-space Neumann factor assertion, not a conclusion
about the differential operator's domain, ranges or self-adjointness. -/
theorem actualRoughL2Potential_both_imaginary_minus_factors_uniform_y
    (u₁ u₂ : PhysicalL2) :
    ∃ y : ℝ, ∃ hy : 1 ≤ y, ∀ n : ℤ,
      ∃ Splus Sminus : SourcePairL2 →L[ℂ] SourcePairL2,
        Splus * (1 - actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂) = 1 ∧
        (1 - actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂) * Splus = 1 ∧
        Sminus * (1 - actualRoughL2PotentialFullNegativeImaginaryResolventCLM n y hy u₁ u₂) = 1 ∧
        (1 - actualRoughL2PotentialFullNegativeImaginaryResolventCLM n y hy u₁ u₂) * Sminus = 1 := by
  let C : ℝ := ‖u₁‖ + ‖u₂‖
  let y : ℝ := 2 * (C + 1) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hy : 1 ≤ y := by
    dsimp [y]
    nlinarith [sq_nonneg (C + 1)]
  have hratio : 2 / y = (1 / (C + 1)) ^ 2 := by
    dsimp [y]
    have hden : C + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hden]
  have hroot : Real.sqrt (2 / y) = 1 / (C + 1) := by
    rw [hratio, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 / (C + 1))]
  have hsmall : Real.sqrt (2 / y) * (‖u₁‖ + ‖u₂‖) < 1 := by
    rw [hroot]
    dsimp [C]
    have hden : 0 < ‖u₁‖ + ‖u₂‖ + 1 := by positivity
    rw [one_div_mul_eq_div]
    exact (div_lt_one hden).2 (by linarith)
  refine ⟨y, hy, ?_⟩
  intro n
  obtain ⟨Splus, hp₁, hp₂⟩ :=
    actualRoughL2PotentialFullImaginaryResolventCLM_minus_two_sided_inverse_of_small
      n y hy u₁ u₂ hsmall
  obtain ⟨Sminus, hm₁, hm₂⟩ :=
    actualRoughL2PotentialFullNegativeImaginaryResolventCLM_minus_two_sided_inverse_of_small
      n y hy u₁ u₂ hsmall
  exact ⟨Splus, Sminus, hp₁, hp₂, hm₁, hm₂⟩

end NlsGge.Schur
end

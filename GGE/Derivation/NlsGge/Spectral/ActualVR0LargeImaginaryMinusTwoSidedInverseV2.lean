import NlsGge.Spectral.ActualFullImaginaryResolventLInfCLMV3
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The manuscript-sign Neumann factor is `1 - V R₀`. Under the explicit
operator-norm decay bound it is a unit on the actual source Hilbert pair. -/
theorem actualRoughL2PotentialFullImaginaryResolventCLM_minus_isUnit
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2)
    (hsmall : Real.sqrt (2 / y) * (‖u₁‖ + ‖u₂‖) < 1) :
    IsUnit (1 - actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂) := by
  let K : SourcePairL2 →L[ℂ] SourcePairL2 :=
    actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂
  have hnorm : ‖K‖ < 1 := by
    dsimp [K]
    exact lt_of_le_of_lt
      (actualRoughL2PotentialFullImaginaryResolventCLM_norm_le n y hy u₁ u₂)
      hsmall
  simpa only [K] using IsUnit.one_sub_of_norm_lt_one hnorm

/-- The actual inverse of the source-space factor `1 - V R₀` has both
two-sided composition identities. This is an endomorphism fact; it does not
yet assert the perturbed differential operator's domain or range. -/
theorem actualRoughL2PotentialFullImaginaryResolventCLM_minus_two_sided_inverse_of_small
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (u₁ u₂ : PhysicalL2)
    (hsmall : Real.sqrt (2 / y) * (‖u₁‖ + ‖u₂‖) < 1) :
    ∃ S : SourcePairL2 →L[ℂ] SourcePairL2,
      S * (1 - actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂) = 1 ∧
      (1 - actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂) * S = 1 := by
  let M : SourcePairL2 →L[ℂ] SourcePairL2 :=
    1 - actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂
  have hunit : IsUnit M := by
    dsimp [M]
    exact actualRoughL2PotentialFullImaginaryResolventCLM_minus_isUnit
      n y hy u₁ u₂ hsmall
  refine ⟨↑hunit.unit⁻¹, ?_, ?_⟩
  · change (↑hunit.unit⁻¹) * M = 1
    exact hunit.val_inv_mul
  · change M * (↑hunit.unit⁻¹) = 1
    exact hunit.mul_val_inv

/-- Every pair of physical L² fields admits a sufficiently large positive
imaginary parameter for which the actual manuscript-sign factor `1 - V R₀`
has a two-sided inverse. The explicit witness has no small-amplitude
assumption; operator-domain/range identification is still a separate step. -/
theorem actualRoughL2PotentialFullImaginaryResolventCLM_minus_exists_large_y_inverse
    (n : ℤ) (u₁ u₂ : PhysicalL2) :
    ∃ y : ℝ, ∃ hy : 1 ≤ y, ∃ S : SourcePairL2 →L[ℂ] SourcePairL2,
      S * (1 - actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂) = 1 ∧
      (1 - actualRoughL2PotentialFullImaginaryResolventCLM n y hy u₁ u₂) * S = 1 := by
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
  obtain ⟨S, hleft, hright⟩ :=
    actualRoughL2PotentialFullImaginaryResolventCLM_minus_two_sided_inverse_of_small
      n y hy u₁ u₂ hsmall
  exact ⟨y, hy, S, hleft, hright⟩

end NlsGge.Schur

end

import NlsGge.Spectral.ActualSourceWeightedDomainPerturbedImaginaryRangeAlgebraV7
import NlsGge.Spectral.ActualUniformBothImaginaryMinusFactorsV2

set_option autoImplicit false
noncomputable section

open NlsGge.Pilot
namespace NlsGge.Schur

/-- For every pair of independent physical L² fields, one actual magnitude
simultaneously gives both imaginary shifted ranges, all sector indices, and
the true source weighted-domain realization of `z - D - V`. -/
theorem actualSourcePerturbedImaginaryShifts_surjective_uniform_y
    (u₁ u₂ : PhysicalL2) :
    ∃ y : ℝ, ∃ hy : 1 ≤ y, ∀ n : ℤ,
      Function.Surjective
        (actualSourcePerturbedShiftedDiracAfterAE n (Complex.I * (y : ℂ)) u₁ u₂) ∧
      Function.Surjective
        (actualSourcePerturbedShiftedDiracAfterAE n (-Complex.I * (y : ℂ)) u₁ u₂) := by
  obtain ⟨y, hy, hfactor⟩ :=
    actualRoughL2Potential_both_imaginary_minus_factors_uniform_y u₁ u₂
  refine ⟨y, hy, ?_⟩
  intro n
  obtain ⟨Splus, Sminus, hpL, hpR, hmL, hmR⟩ := hfactor n
  constructor
  · apply actualSourcePerturbedPositiveImaginaryShift_surjective_of_factor_right_inverse
      n y hy u₁ u₂ Splus
    intro x
    have h := congrArg (fun T : SourcePairL2 →L[ℂ] SourcePairL2 => T x) hpR
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  · apply actualSourcePerturbedNegativeImaginaryShift_surjective_of_factor_right_inverse
      n y hy u₁ u₂ Sminus
    intro x
    have h := congrArg (fun T : SourcePairL2 →L[ℂ] SourcePairL2 => T x) hmR
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

end NlsGge.Schur

end

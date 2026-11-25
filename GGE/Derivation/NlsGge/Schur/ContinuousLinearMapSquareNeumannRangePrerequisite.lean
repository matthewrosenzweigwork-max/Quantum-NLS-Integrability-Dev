import NlsGge.Schur.FreeResolventSquareNeumannAfterScalarPrerequisites
import NlsGge.Schur.FreeResolventInverseProjectionSupportPrerequisites

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- A square-small endomorphism supported on both sides by an idempotent
projection has a Neumann inverse that preserves the projection range. The
concrete application supplies the actual complementary factors and their
proved norm bounds; this lemma performs only the inverse and range algebra. -/
theorem continuousLinearMap_square_neumann_inverse_preserves_projection_range
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E]
    (Q A : E →L[ℂ] E) (B C : ℝ)
    (hQ2 : Q.comp Q = Q)
    (hAQ : A.comp Q = A) (hQA : Q.comp A = A)
    (hB : 0 ≤ B) (hA : ‖A‖ ≤ B) (hA2 : ‖A * A‖ ≤ (1 / 2 : ℝ))
    (hbound : 2 * (1 + B) ≤ C) :
    ∃ S : E →L[ℂ] E,
      S * (1 - A) = 1 ∧ (1 - A) * S = 1 ∧
      Q.comp S = S.comp Q ∧
      (∀ x, Q x = x → Q (S x) = S x) ∧
      (∀ x, x ∈ Set.range Q → S x ∈ Set.range Q) ∧
      (∀ x, x ∈ Set.range Q ↔ Q x = x) ∧
      ‖S‖ ≤ C := by
  obtain ⟨S, hSright, hSleft, hSnorm⟩ :=
    continuousLinearMap_square_neumann_inverse A B hB hA hA2
  have hAQmul : A * Q = A := by
    simpa only [ContinuousLinearMap.mul_def] using hAQ
  have hQAmul : Q * A = A := by
    simpa only [ContinuousLinearMap.mul_def] using hQA
  have hScommMul : Q * S = S * Q :=
    inverse_commutes_with_bilateral_projection_support Q A S hAQmul hQAmul
      hSright hSleft
  have hScomm : Q.comp S = S.comp Q := by
    simpa only [ContinuousLinearMap.mul_def] using hScommMul
  have hFixed : ∀ x, Q x = x → Q (S x) = S x := by
    intro x hx
    have h := congrArg (fun T : E →L[ℂ] E => T x) hScomm
    simpa only [ContinuousLinearMap.comp_apply, hx] using h
  have hRangeEq : ∀ x, x ∈ Set.range Q ↔ Q x = x := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      have h := congrArg (fun T : E →L[ℂ] E => T y) hQ2
      simpa only [ContinuousLinearMap.comp_apply] using h
    · intro hx
      exact ⟨x, hx⟩
  have hSrange : ∀ x, x ∈ Set.range Q → S x ∈ Set.range Q := by
    intro x hx
    rcases hx with ⟨y, hy⟩
    refine ⟨S y, ?_⟩
    have h := congrArg (fun T : E →L[ℂ] E => T y) hScomm
    simpa only [ContinuousLinearMap.comp_apply, hy] using h
  exact ⟨S, hSright, hSleft, hScomm, hFixed, hSrange, hRangeEq,
    hSnorm.trans hbound⟩

end NlsGge.Schur

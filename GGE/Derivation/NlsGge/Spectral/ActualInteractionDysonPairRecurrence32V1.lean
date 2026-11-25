import NlsGge.Spectral.ActualInteractionDysonParity32V1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations

/-- Both even diagonal entries satisfy the actual two-step integral recurrence.
This is an identity of the defined Picard iterates, with the off-diagonal
condition explicitly realized below for the concrete source coefficient. It
does not assert a triangle bound or high-energy normalization. -/
theorem genericOffDiagonalDyson_pair_recurrence32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hdiag : ∀ t, B t 0 0 = 0 ∧ B t 1 1 = 0)
    (k : ℕ) (t : ℝ) :
    genericRoughMatrixDysonTerm32 B (2*k+2) t 0 0 =
      (∫ s in (0 : ℝ)..t, B s 0 1 *
        (∫ r in (0 : ℝ)..s, B r 1 0 *
          genericRoughMatrixDysonTerm32 B (2*k) r 0 0)) ∧
    genericRoughMatrixDysonTerm32 B (2*k+2) t 1 1 =
      (∫ s in (0 : ℝ)..t, B s 1 0 *
        (∫ r in (0 : ℝ)..s, B r 0 1 *
          genericRoughMatrixDysonTerm32 B (2*k) r 1 1)) := by
  have h00 (s : ℝ) := (hdiag s).1
  have h11 (s : ℝ) := (hdiag s).2
  have h10 (s : ℝ) : genericRoughMatrixDysonTerm32 B (2*k+1) s 1 0 =
      (∫ r in (0 : ℝ)..s, B r 1 0 * genericRoughMatrixDysonTerm32 B (2*k) r 0 0) := by
    change (∫ r in (0 : ℝ)..s, (B r * genericRoughMatrixDysonTerm32 B (2*k) r) 1 0) = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h11, zero_mul, add_zero]
  have h01 (s : ℝ) : genericRoughMatrixDysonTerm32 B (2*k+1) s 0 1 =
      (∫ r in (0 : ℝ)..s, B r 0 1 * genericRoughMatrixDysonTerm32 B (2*k) r 1 1) := by
    change (∫ r in (0 : ℝ)..s, (B r * genericRoughMatrixDysonTerm32 B (2*k) r) 0 1) = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h00, zero_mul, zero_add]
  constructor
  · change (∫ s in (0 : ℝ)..t, (B s * genericRoughMatrixDysonTerm32 B (2*k+1) s) 0 0) = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h00, zero_mul, zero_add, h10]
  · change (∫ s in (0 : ℝ)..t, (B s * genericRoughMatrixDysonTerm32 B (2*k+1) s) 1 1) = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two, h11, zero_mul, add_zero, h01]

/-- No diagonal-support hypothesis remains for the original concrete U/star(U)
interaction coefficient. This holds for every complex spectral parameter. -/
theorem actualInteractionDyson_pair_recurrence32
    (U : ℝ → ℂ) (z : ℂ) (k : ℕ) (t : ℝ) :
    genericRoughMatrixDysonTerm32 (actualZsInteractionCoefficient32 U z) (2*k+2) t 0 0 =
      (∫ s in (0 : ℝ)..t, actualZsInteractionCoefficient32 U z s 0 1 *
        (∫ r in (0 : ℝ)..s, actualZsInteractionCoefficient32 U z r 1 0 *
          genericRoughMatrixDysonTerm32 (actualZsInteractionCoefficient32 U z) (2*k) r 0 0)) ∧
    genericRoughMatrixDysonTerm32 (actualZsInteractionCoefficient32 U z) (2*k+2) t 1 1 =
      (∫ s in (0 : ℝ)..t, actualZsInteractionCoefficient32 U z s 1 0 *
        (∫ r in (0 : ℝ)..s, actualZsInteractionCoefficient32 U z r 0 1 *
          genericRoughMatrixDysonTerm32 (actualZsInteractionCoefficient32 U z) (2*k) r 1 1)) := by
  apply genericOffDiagonalDyson_pair_recurrence32
  intro s
  simp [actualZsInteractionCoefficient32]

end NlsGge.SpectralFoundations
end

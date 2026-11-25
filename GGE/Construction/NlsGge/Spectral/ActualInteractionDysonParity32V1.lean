import NlsGge.Spectral.ActualPhysicalInteractionDysonIdentification32V2
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations

/-- Actual left-ordered iterates alternate diagonal and off-diagonal support
for EVERY off-diagonal coefficient. No field regularity or target parity is
assumed: this follows from the recurrence and the coefficient entries. -/
theorem genericOffDiagonalDyson_parity32
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hdiag : ∀ t, B t 0 0 = 0 ∧ B t 1 1 = 0) :
    ∀ k : ℕ, ∀ t : ℝ,
      genericRoughMatrixDysonTerm32 B (2*k) t 0 1 = 0 ∧
      genericRoughMatrixDysonTerm32 B (2*k) t 1 0 = 0 ∧
      genericRoughMatrixDysonTerm32 B (2*k+1) t 0 0 = 0 ∧
      genericRoughMatrixDysonTerm32 B (2*k+1) t 1 1 = 0 := by
  have h00 (s : ℝ) := (hdiag s).1
  have h11 (s : ℝ) := (hdiag s).2
  intro k
  induction k with
  | zero =>
      intro t
      simp [genericRoughMatrixDysonTerm32, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.one_apply, h00, h11]
  | succ k ih =>
      have ho00 (s : ℝ) := (ih s).2.2.1
      have ho11 (s : ℝ) := (ih s).2.2.2
      have he01 (s : ℝ) : genericRoughMatrixDysonTerm32 B (2*(k+1)) s 0 1 = 0 := by
        rw [show 2*(k+1) = (2*k+1)+1 by omega]
        change (∫ x in (0 : ℝ)..s, (B x * genericRoughMatrixDysonTerm32 B (2*k+1) x) 0 1) = 0
        simp only [Matrix.mul_apply, Fin.sum_univ_two, h00, ho11,
          zero_mul, mul_zero, add_zero, intervalIntegral.integral_zero]
      have he10 (s : ℝ) : genericRoughMatrixDysonTerm32 B (2*(k+1)) s 1 0 = 0 := by
        rw [show 2*(k+1) = (2*k+1)+1 by omega]
        change (∫ x in (0 : ℝ)..s, (B x * genericRoughMatrixDysonTerm32 B (2*k+1) x) 1 0) = 0
        simp only [Matrix.mul_apply, Fin.sum_univ_two, h11, ho00,
          zero_mul, mul_zero, add_zero, intervalIntegral.integral_zero]
      intro t
      refine ⟨he01 t, he10 t, ?_, ?_⟩
      · change (∫ x in (0 : ℝ)..t, (B x * genericRoughMatrixDysonTerm32 B (2*(k+1)) x) 0 0) = 0
        simp only [Matrix.mul_apply, Fin.sum_univ_two, h00, he10,
          zero_mul, mul_zero, add_zero, intervalIntegral.integral_zero]
      · change (∫ x in (0 : ℝ)..t, (B x * genericRoughMatrixDysonTerm32 B (2*(k+1)) x) 1 1) = 0
        simp only [Matrix.mul_apply, Fin.sum_univ_two, h11, he01,
          zero_mul, mul_zero, add_zero, intervalIntegral.integral_zero]

/-- Odd diagonal interaction terms vanish for the ORIGINAL concrete U/star(U)
ZS interaction coefficient. This prerequisite alone is not the all-even
trace bound or high-energy quasimomentum normalization. -/
theorem actualInteractionDyson_odd_diagonal_zero32
    (U : ℝ → ℂ) (z : ℂ) (k : ℕ) (t : ℝ) :
    genericRoughMatrixDysonTerm32 (actualZsInteractionCoefficient32 U z) (2*k+1) t 0 0 = 0 ∧
    genericRoughMatrixDysonTerm32 (actualZsInteractionCoefficient32 U z) (2*k+1) t 1 1 = 0 := by
  have hd : ∀ s, actualZsInteractionCoefficient32 U z s 0 0 = 0 ∧
      actualZsInteractionCoefficient32 U z s 1 1 = 0 := by
    intro s
    simp [actualZsInteractionCoefficient32]
  exact (genericOffDiagonalDyson_parity32 (actualZsInteractionCoefficient32 U z) hd k t).2.2

end NlsGge.SpectralFoundations
end

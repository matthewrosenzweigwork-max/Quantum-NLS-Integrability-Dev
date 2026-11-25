import QuantumNLS.Local002Neumann
import Mathlib.Analysis.Analytic.Constructions

/-! The square-small Neumann step in GLOBAL-B01. This is an algebraic
building block: the source's high-frequency estimate and the realization of
its operator family are separate obligations. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound35SquareInverse

/-- Square-smallness suffices even when the operator itself need not have norm
below one. The two-sided inverse has the source's factorization and bound. -/
theorem square_small_inverse {A : Type*} [NormedRing A] [CompleteSpace A]
    (h1n : ‖(1 : A)‖ ≤ 1) (T : A) (hT : ‖T * T‖ < 1) :
    ∃ S : A, (1 - T) * S = 1 ∧ S * (1 - T) = 1 ∧
      ‖S‖ ≤ (1 + ‖T‖) * (1 - ‖T * T‖)⁻¹ := by
  obtain ⟨Q, hQ1, hQ2, hQn⟩ := QuantumNLS.Local002.exists_inv_one_sub h1n (T * T) hT
  have hf : (1 - T) * (1 + T) = 1 - T * T := by noncomm_ring
  have hf' : (1 + T) * (1 - T) = 1 - T * T := by noncomm_ring
  have hr : (1 - T) * ((1 + T) * Q) = 1 := by rw [← mul_assoc, hf, hQ1]
  have hl : (Q * (1 + T)) * (1 - T) = 1 := by rw [mul_assoc, hf', hQ2]
  have heq : Q * (1 + T) = (1 + T) * Q := by
    calc
      Q * (1 + T) = (Q * (1 + T)) * ((1 - T) * ((1 + T) * Q)) := by rw [hr, mul_one]
      _ = ((Q * (1 + T)) * (1 - T)) * ((1 + T) * Q) := by simp only [mul_assoc]
      _ = (1 + T) * Q := by rw [hl, one_mul]
  refine ⟨(1 + T) * Q, hr, ?_, ?_⟩
  · rw [← heq]; exact hl
  · calc
      ‖(1 + T) * Q‖ ≤ ‖1 + T‖ * ‖Q‖ := norm_mul_le _ _
      _ ≤ (1 + ‖T‖) * (1 - ‖T * T‖)⁻¹ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add h1n le_rfl)

/-- On the open square-small region the inverse of an analytic operator
family is analytic. This does not assert square-smallness for the spectral
operator; that field-dependent estimate must be proved separately. -/
theorem analytic_inverse_of_square_small {E A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (h1n : ‖(1 : A)‖ ≤ 1) {F : E → A} {x : E}
    (hF : AnalyticAt ℂ F x) (hsmall : ‖F x * F x‖ < 1) :
    AnalyticAt ℂ (fun y => Ring.inverse (1 - F y)) x := by
  obtain ⟨S, hS1, hS2, -⟩ := square_small_inverse h1n (F x) hsmall
  let u : Aˣ := ⟨1 - F x, S, hS1, hS2⟩
  have hi : AnalyticAt ℂ (Ring.inverse : A → A) (1 - F x) := by
    exact analyticAt_inverse (𝕜 := ℂ) u
  have ha : AnalyticAt ℂ (fun y : E => (1 : A) - F y) x :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : E => (1 : A)) x).sub hF
  exact AnalyticAt.comp (f := fun y : E => (1 : A) - F y) (x := x) hi ha

end QuantumNLS.TerraMultiRound35SquareInverse
#print axioms QuantumNLS.TerraMultiRound35SquareInverse.square_small_inverse
#print axioms QuantumNLS.TerraMultiRound35SquareInverse.analytic_inverse_of_square_small

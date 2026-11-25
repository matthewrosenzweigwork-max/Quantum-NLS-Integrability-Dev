import Mathlib

/-! The perturbation estimate used to pass from finite Fourier support to a
fixed arbitrary field in GLOBAL-B01. This is the algebraic inequality; no
Fourier approximation or high-frequency decay is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound35SquareStability

/-- Exact square perturbation bound, valid for noncommuting operators. -/
theorem square_add_bound {A : Type*} [NormedRing A] (a b : A) :
    ‖(a + b) * (a + b) - a * a‖ ≤ 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 := by
  have e : (a + b) * (a + b) - a * a = a * b + b * a + b * b := by
    noncomm_ring
  rw [e]
  calc
    ‖a * b + b * a + b * b‖ ≤ ‖a * b‖ + ‖b * a‖ + ‖b * b‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖a‖ * ‖b‖ + ‖b‖ * ‖a‖ + ‖b‖ * ‖b‖ := by
      gcongr <;> apply norm_mul_le
    _ = 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 := by ring

end QuantumNLS.TerraMultiRound35SquareStability
#print axioms QuantumNLS.TerraMultiRound35SquareStability.square_add_bound

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati

open scoped ComplexConjugate

/-- Iterated real derivatives commute with complex conjugation. -/
theorem iteratedDeriv_star_prerequisite (u : ℝ → ℂ) (n : ℕ) :
    iteratedDeriv n (fun x => star (u x)) =
      fun x => star (iteratedDeriv n u x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
      exact deriv.star'

end NlsGge.HierarchyRiccati

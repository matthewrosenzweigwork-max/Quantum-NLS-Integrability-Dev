import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

set_option autoImplicit false

namespace NlsGge.HierarchyRiccati

open scoped ContDiff

private theorem periodic_deriv_of_contDiff
    {f : ℝ → ℂ} {T : ℝ}
    (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  have hbase : HasDerivAt f (deriv f x) x :=
    ((hf.differentiable (by simp)).differentiableAt).hasDerivAt
  have hshiftAt : HasDerivAt f (deriv f (x + T)) (x + T) :=
    ((hf.differentiable (by simp)).differentiableAt).hasDerivAt
  have hshift : HasDerivAt (fun y => f (y + T))
      (deriv f (x + T)) x := hshiftAt.comp_add_const x T
  have hfun : (fun y => f (y + T)) = f := funext hper
  rw [hfun] at hshift
  exact hshift.unique hbase

private theorem iteratedDeriv_contDiff_of_contDiff
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv n hf

/-- A smooth periodic function has periodic iterated derivatives. The proof
uses translation invariance of `HasDerivAt` and derivative uniqueness at each
order, rather than assuming derivative periodicity as extra data. -/
theorem periodic_iteratedDeriv_of_contDiff
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f 1) (n : ℕ) :
    Function.Periodic (iteratedDeriv n f) 1 := by
  induction n with
  | zero => simpa using hper
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact periodic_deriv_of_contDiff
        (iteratedDeriv_contDiff_of_contDiff f hf n) ih

end NlsGge.HierarchyRiccati

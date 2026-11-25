import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import NlsGge.Schur.SourceInterval

/-! The distributional derivative graph on the unit interval.
This carrier imposes no endpoint condition and contains no representative or trace assumption.
The representative and trace theorems remain the obligations of LIB-026. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace NlsGge.Atomic.Interval

/-- Distributional derivative against real smooth compactly supported tests
in the open unit interval. Complex-valued identities encode both real components. -/
def HasWeakDerivative (f g : ℝ → ℂ) : Prop :=
  ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Ioo (0 : ℝ) 1 →
      (∫ x in (0 : ℝ)..1, f x * ((deriv ψ x : ℝ) : ℂ)) =
        -(∫ x in (0 : ℝ)..1, g x * (ψ x : ℂ))

/-- The graph of the weak derivative in interval L², with no boundary relation. -/
structure H1 where
  value : NlsGge.Schur.SourceIntervalL2
  derivative : NlsGge.Schur.SourceIntervalL2
  weak : HasWeakDerivative value derivative

end NlsGge.Atomic.Interval

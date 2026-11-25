import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

/-! Small pinned-API node isolating the complex-valued product rule used by
the smooth formal-jet evaluator. Keeping the typeclass-polymorphic product
rule behind a named theorem lets downstream code instantiate it from the
expected `HasDerivAt` goal rather than synthesizing a second module action. -/

namespace NlsGge.HierarchyRiccati

theorem hasDerivAt_mul_complex_core
    {f g : ℝ → ℂ} {f' g' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y * g y) (f' * g x + f x * g') x := by
  exact hf.mul hg

end NlsGge.HierarchyRiccati

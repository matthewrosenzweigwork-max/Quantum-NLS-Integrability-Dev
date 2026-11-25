import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
The additive-group compactness API bounds the norm of a continuous complex
valued function. This isolates the exact real/complex topology dictionary
needed by the concrete ZS coefficient estimate.
-/

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

theorem exists_bound_complex_norm_of_continuousOn
    (u : ℝ → ℂ) (hu : ContinuousOn u (Set.Icc (0 : ℝ) 2)) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 2, ‖u x‖ ≤ C := by
  exact IsCompact.exists_bound_of_continuousOn
    (α := ℝ) (E := ℂ) (s := Set.Icc (0 : ℝ) 2) (f := u)
    isCompact_Icc hu

end NlsGge.SpectralFoundations

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
Scalar inequality used by the arbitrary-state Picard step.  This isolates
the denominator multiplication from the ODE assembly.
-/

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

theorem four_mul_coefficient_mul_step_le_one
    (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hδsmall : δ ≤ 1 / (4 * C + 1)) :
    4 * C * δ ≤ 1 := by
  have hdenpositive : 0 < 4 * C + 1 := by positivity
  have hδmul : δ * (4 * C + 1) ≤ 1 :=
    (le_div_iff₀ hdenpositive).1 hδsmall
  calc
    4 * C * δ ≤ δ * (4 * C + 1) := by nlinarith
    _ ≤ 1 := hδmul

end NlsGge.SpectralFoundations

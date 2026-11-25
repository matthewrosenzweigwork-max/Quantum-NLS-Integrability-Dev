import NlsGge.Sobolev.WeightedHilbert
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot

/-- The unit-weight realization in `lp` evaluates to the original Fourier
coordinate. This records the carrier coercion explicitly for the derivative
CLM Fourier identity. -/
theorem weightedL2Element_unit_coordinateMinimumRecovery30
    (x : ℤ → ℂ) (hx : Summable (fun n : ℤ => ‖x n‖ ^ 2)) (n : ℤ) :
    (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num) x
      (by simpa only [one_mul] using hx) : lp (fun _ : ℤ => ℂ) 2) n = x n := by
  change weightedCoordinates (fun _ : ℤ => (1 : ℝ)) x n = x n
  simp [weightedCoordinates]

end NlsGge.Pilot

end

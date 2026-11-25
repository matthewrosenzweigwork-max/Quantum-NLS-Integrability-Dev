                                                                                                                                                                                                                                                                                 
import Mathlib
import NlsGge.Weights.StirlingBounds

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.R
noncomputable section

theorem factorial_stirling_bounds :
    ∃ cS : ℝ, cS > 0 ∧ ∃ CS : ℝ, CS > 0 ∧ ∀ j : ℕ, 1 ≤ j →
      cS * Real.sqrt (j : ℝ) * ((j : ℝ) / Real.exp 1) ^ j ≤ (j.factorial : ℝ) ∧
      (j.factorial : ℝ) ≤ CS * Real.sqrt (j : ℝ) * ((j : ℝ) / Real.exp 1) ^ j :=
  ⟨Real.sqrt (2 * Real.pi), by positivity, Real.exp 1, by positivity,
    fun j hj => NlsGge.Weights.factorial_stirling_bounds j hj⟩


end
end NlsGge.ThirdConsultation.R

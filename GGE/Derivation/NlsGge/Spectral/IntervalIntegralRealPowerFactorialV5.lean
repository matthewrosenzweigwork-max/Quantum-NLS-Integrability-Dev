import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

/-- The elementary scalar integral underlying the factorial majorant for
ordered Picard integrals. -/
theorem intervalIntegral_zero_to_t_real_pow (n : ℕ) (t : ℝ) :
    (∫ x in (0 : ℝ)..t, x ^ n) = t ^ (n + 1) / (n + 1 : ℝ) := by
  rw [integral_pow]
  simp

end NlsGge.SpectralFoundations

end

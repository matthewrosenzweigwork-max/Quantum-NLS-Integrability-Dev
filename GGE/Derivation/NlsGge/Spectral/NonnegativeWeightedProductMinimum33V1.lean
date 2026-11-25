import Mathlib.Tactic
set_option autoImplicit false
namespace NlsGge.SpectralFoundations
/-- Exact scalar multiplication minimum isolated from the actual weighted
Volterra bound after its three preserved elaboration attempts. -/
theorem nonnegativeWeightedProduct_minimum33
    (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hcd : c ≤ d) :
    a*b*c ≤ d*(b*a) := by
  have h : a*b*c ≤ a*b*d := mul_le_mul_of_nonneg_left hcd (mul_nonneg ha hb)
  nlinarith only [h]
end NlsGge.SpectralFoundations

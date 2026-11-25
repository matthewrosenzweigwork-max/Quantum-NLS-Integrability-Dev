import QuantumNLS.TerraMultiRound64REG004

/-! Pointwise algebra behind the fourth-moment correction. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace QuantumNLS.TerraMultiRound65FourthAlgebra

/-- The printed first-order interaction is the real polynomial obtained after
integration by parts.  The last square is the squared derivative of |u|²
when `w` represents u'. -/
theorem quartic_integrand_identity (z w : ℂ) :
    z^2 * (conj w)^2 + 8 * ((‖z‖^2 * ‖w‖^2 : ℝ) : ℂ) + (conj z)^2 * w^2 =
      6 * ((‖z‖^2 * ‖w‖^2 : ℝ) : ℂ) + (conj w * z + conj z * w)^2 := by
  have hz : conj z * z = ((‖z‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hw : conj w * w = ((‖w‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast at hz hw ⊢
  rw [← hz, ← hw]
  ring

#print axioms quartic_integrand_identity
end QuantumNLS.TerraMultiRound65FourthAlgebra

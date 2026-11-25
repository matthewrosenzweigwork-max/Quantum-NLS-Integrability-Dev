import QuantumNLS.TerraMultiRound65FourthAlgebra
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Classical derivative of the squared density and its pointwise correction. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open QuantumNLS.TerraMultiRound65FourthAlgebra
namespace QuantumNLS.TerraMultiRound65DensityDerivative

/-- For a differentiable complex field, the complex embedding of |u|² has the
expected real derivative. -/
theorem density_hasDerivAt {f : ℝ → ℂ} {x : ℝ} {v : ℂ} (h : HasDerivAt f v x) :
    HasDerivAt (fun y => ((‖f y‖^2 : ℝ) : ℂ))
      (conj v * f x + conj (f x) * v) x := by
  have hd := h.star.mul h
  convert hd using 1
  funext y
  change ((‖f y‖^2 : ℝ) : ℂ) = conj (f y) * f y
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rfl

/-- The expanded and density-derivative forms of the quartic integrand agree
at each differentiability point. -/
theorem correction_at_point {f : ℝ → ℂ} {x : ℝ} (h : DifferentiableAt ℝ f x) :
    f x^2 * (conj (deriv f x))^2 +
      8 * ((‖f x‖^2 * ‖deriv f x‖^2 : ℝ) : ℂ) +
      (conj (f x))^2 * (deriv f x)^2 =
    6 * ((‖f x‖^2 * ‖deriv f x‖^2 : ℝ) : ℂ) +
      (deriv (fun y => ((‖f y‖^2 : ℝ) : ℂ)) x)^2 := by
  rw [(density_hasDerivAt h.hasDerivAt).deriv]
  exact quartic_integrand_identity (f x) (deriv f x)

#print axioms density_hasDerivAt
#print axioms correction_at_point
end QuantumNLS.TerraMultiRound65DensityDerivative

import QuantumNLS.Local001Sup

set_option autoImplicit false
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.LocalSpectral

/-- The off-diagonal potential matrix in the source equation. -/
def potentialPt (κ : ℝ) (w : ℂ) (g : E2) : E2 :=
  vec2 (-(2 * Complex.I) * (Real.sqrt κ : ℂ) * conj w * g 1)
    ((2 * Complex.I) * (Real.sqrt κ : ℂ) * w * g 0)

/-- Exact pointwise size of the source potential matrix. -/
theorem potentialPt_norm_sq {κ : ℝ} (hκ : 0 ≤ κ) (w : ℂ) (g : E2) :
    ‖potentialPt κ w g‖ ^ 2 =
      (2 * Real.sqrt κ * ‖w‖) ^ 2 * ‖g‖ ^ 2 := by
  have hsqrt : ‖(Real.sqrt κ : ℂ)‖ = Real.sqrt κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg κ)]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [potentialPt, LocalSpectral.vec2, Fin.sum_univ_two, norm_mul,
    Complex.norm_conj, Complex.norm_I, hsqrt, abs_of_nonneg (Real.sqrt_nonneg κ)]
  ring

/-- The pointwise source potential norm is `2√κ |u(x)|` times the input norm. -/
theorem potentialPt_norm {κ : ℝ} (hκ : 0 ≤ κ) (w : ℂ) (g : E2) :
    ‖potentialPt κ w g‖ = 2 * Real.sqrt κ * ‖w‖ * ‖g‖ := by
  have hsq := potentialPt_norm_sq hκ w g
  have hA : 0 ≤ 2 * Real.sqrt κ * ‖w‖ * ‖g‖ := by positivity
  have hnorm : 0 ≤ ‖potentialPt κ w g‖ := norm_nonneg _
  have hprod : (‖potentialPt κ w g‖ - (2 * Real.sqrt κ * ‖w‖ * ‖g‖)) *
      (‖potentialPt κ w g‖ + (2 * Real.sqrt κ * ‖w‖ * ‖g‖)) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.mp hprod with hdiff | hsum
  · linarith
  · linarith

#print axioms potentialPt_norm_sq
#print axioms potentialPt_norm

end QuantumNLS.ResetFreeResolventLOCAL001

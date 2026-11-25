import NlsGge.Spectral.FreeZakharovShabatFundamentalComplexV4
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations

/-- The exact current used for the original source first-order system. -/
def actualZsIndefiniteCurrent33 (v : Fin 2 → ℂ) : ℂ :=
  v 0 * star (v 0) - v 1 * star (v 1)

/-- Exact algebra behind the actual rough-flow current derivative. The
original complex off-diagonal U/starU pair cancels; no reality of U or z,
regularity of a source representative, or spectral conclusion is assumed. -/
theorem actualZsIndefiniteCurrent_derivative_algebra33
    (U : ℝ → ℂ) (z : ℂ) (t : ℝ) (v : Fin 2 → ℂ) :
    let w : Fin 2 → ℂ := (zsCoefficientComplex U z t).mulVec v
    (w 0 * star (v 0) + v 0 * star (w 0)) -
      (w 1 * star (v 1) + v 1 * star (w 1)) =
    ((2 * z.im : ℝ) : ℂ) * (v 0 * star (v 0) + v 1 * star (v 1)) := by
  dsimp only
  apply Complex.ext <;>
    simp [zsCoefficientComplex, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

/-- Every unit-modulus scalar preserves the REAL current at an endpoint.
This includes arbitrary Floquet phases, not only the signed parities. It is
still an endpoint algebra fact, not the nonreal-multiplier exclusion. -/
theorem actualZsUnitScalar_preserves_realCurrent33
    (χ : ℂ) (hχ : ‖χ‖ = 1) (v : Fin 2 → ℂ) :
    ‖χ * v 0‖ ^ 2 - ‖χ * v 1‖ ^ 2 = ‖v 0‖ ^ 2 - ‖v 1‖ ^ 2 := by
  simp only [norm_mul, hχ, one_mul]

end NlsGge.SpectralFoundations
end

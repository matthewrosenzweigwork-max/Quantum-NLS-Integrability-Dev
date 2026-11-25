import NlsGge.Spectral.FreeZakharovShabatFundamentalComplexV4
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations

/-- Cancellation for the actual complex ZS coefficient, including its
conjugated lower-left entry. This is the determinant derivative algebra,
not existence of a fundamental solution. -/
theorem actualComplexZsDeterminantDerivative_cancel
    (u : ℝ → ℂ) (z : ℂ) (x : ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (zsCoefficientComplex u z x * M) 0 0 * M 1 1 +
        M 0 0 * (zsCoefficientComplex u z x * M) 1 1 -
      ((zsCoefficientComplex u z x * M) 0 1 * M 1 0 +
        M 0 1 * (zsCoefficientComplex u z x * M) 1 0) = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, zsCoefficientComplex,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const]
  ring

/-- At a point where the four genuine entrywise ZS equations hold, the
determinant has derivative zero. The equations are explicit hypotheses;
rough-L² existence and AE realization are separate checked dependencies. -/
theorem actualComplexZsDeterminant_hasDerivAt_zero
    (u : ℝ → ℂ) (z : ℂ)
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ)
    (h : ∀ i j : Fin 2, HasDerivAt (fun t => F t i j)
      ((zsCoefficientComplex u z x * F x) i j) x) :
    HasDerivAt (fun t => Matrix.det (F t)) 0 x := by
  have hd := ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0))
  rw [actualComplexZsDeterminantDerivative_cancel u z x (F x)] at hd
  simpa only [Matrix.det_fin_two, Pi.mul_apply, Pi.sub_apply] using! hd
end NlsGge.SpectralFoundations
end

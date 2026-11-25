import NlsGge.Spectral.FreeZakharovShabatScalarExponentialEvaluationV2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
Exact free-potential solution and period-specific traces for the complex
spectral parameter. This uses the separately proved scalar-coordinate bridge;
it does not construct the nonconstant-potential fundamental solution or any
quasimomentum/gap data.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

/-- The complex spectral-parameter extension of the paper's coefficient. -/
def zsCoefficientComplex (u : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(-Complex.I * z), (Complex.I * u x);
    (-Complex.I * star (u x)), (Complex.I * z)]

theorem zsCoefficientComplex_ofReal (u : ℝ → ℂ) (realParam : ℝ) (x : ℝ) :
    zsCoefficientComplex u (realParam : ℂ) x = zsCoefficient u realParam x := rfl

/-- Fundamental-solution predicate at complex spectral parameter `z`. -/
def IsZsFundamentalSolutionComplex (u : ℝ → ℂ) (z : ℂ)
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  F 0 = 1 ∧ ∀ x : ℝ,
    HasDerivAt F (zsCoefficientComplex u z x * F x) x

/-- Exact free-field fundamental matrix, with `x` as real evolution time. -/
def freeZsFundamentalComplex (z : ℂ) (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ := freeDiagonalCandidate z x

theorem zsCoefficientComplex_zero (z : ℂ) (x : ℝ) :
    zsCoefficientComplex (fun _ => 0) z x = freeZeroCoefficientCandidate z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zsCoefficientComplex, freeZeroCoefficientCandidate, Matrix.diagonal]

theorem freeZsFundamentalComplex_is (z : ℂ) :
    IsZsFundamentalSolutionComplex (fun _ => 0) z
      (freeZsFundamentalComplex z) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [freeZsFundamentalComplex, freeDiagonalCandidate, Matrix.diagonal]
  · intro x
    change HasDerivAt
      (fun t : ℝ => fun i : Fin 2 => fun j : Fin 2 =>
        freeZsFundamentalComplex z t i j)
      (fun i : Fin 2 => fun j : Fin 2 =>
        (zsCoefficientComplex (fun _ => 0) z x * freeZsFundamentalComplex z x) i j) x
    apply (hasDerivAt_pi (𝕜 := ℝ)).2
    intro i
    apply (hasDerivAt_pi (𝕜 := ℝ)).2
    intro j
    fin_cases i <;> fin_cases j
    · rw [zsCoefficientComplex_zero]
      simpa [freeZsFundamentalComplex] using
        (freeDiagonalCandidate_hasDerivAt_00 z x)
    · simpa [freeZsFundamentalComplex, zsCoefficientComplex,
        freeDiagonalCandidate, Matrix.diagonal_mul_diagonal] using
        (hasDerivAt_const x (0 : ℂ))
    · simpa [freeZsFundamentalComplex, zsCoefficientComplex,
        freeDiagonalCandidate, Matrix.diagonal_mul_diagonal] using
        (hasDerivAt_const x (0 : ℂ))
    · rw [zsCoefficientComplex_zero]
      simpa [freeZsFundamentalComplex] using
        (freeDiagonalCandidate_hasDerivAt_11 z x)

/-- Full, unhalved free monodromy trace for an arbitrary real period. -/
theorem freeZsFullTraceComplex (z : ℂ) (period : ℝ) :
    zsFullTrace (freeZsFundamentalComplex z) period =
      Complex.exp (period • (-Complex.I * z)) +
        Complex.exp (period • (Complex.I * z)) := by
  simp [zsFullTrace, zsMonodromy, freeZsFundamentalComplex,
    freeDiagonalCandidate, Matrix.trace_diagonal]

/-- The free fundamental matrix has determinant one at every time. -/
theorem freeZsFundamentalComplex_det (z : ℂ) (x : ℝ) :
    Matrix.det (freeZsFundamentalComplex z x) = 1 := by
  have hsum : x • (-Complex.I * z) + x • (Complex.I * z) = 0 := by
    rw [← smul_add]
    rw [show (-Complex.I * z) + (Complex.I * z) = 0 by ring]
    simp only [smul_zero]
  rw [freeZsFundamentalComplex, freeDiagonalCandidate, Matrix.det_fin_two]
  simp [Matrix.diagonal, hsum, ← Complex.exp_add]

end NlsGge.SpectralFoundations

import NlsGge.Spectral.ConcreteZakharovShabatODEObjectsV4

/-!
The scalar coordinate bridge for the free complex ZS fundamental matrix.
This isolates the two diagonal coordinate derivative/evaluation conversions;
it does not assert the matrix-valued fundamental-solution theorem.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

/-- The free complex solution's diagonal matrix, written without a matrix literal. -/
def freeDiagonalCandidate (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i : Fin 2 =>
    if i = 0 then Complex.exp (t • (-Complex.I * z))
    else Complex.exp (t • (Complex.I * z)))

/-- The zero-potential coefficient matrix at complex parameter `z`. -/
def freeZeroCoefficientCandidate (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i : Fin 2 =>
    if i = 0 then -Complex.I * z else Complex.I * z)

/-- The `(0,0)` coordinate has the actual zero-field matrix derivative. -/
theorem freeDiagonalCandidate_hasDerivAt_00 (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => freeDiagonalCandidate z t 0 0)
      ((freeZeroCoefficientCandidate z * freeDiagonalCandidate z x) 0 0) x := by
  have h := ((hasDerivAt_id' x).smul_const (-Complex.I * z)).cexp
  apply h.congr_deriv
  simp [freeZeroCoefficientCandidate, freeDiagonalCandidate,
    Matrix.diagonal_mul_diagonal, mul_comm]

/-- The `(1,1)` coordinate has the actual zero-field matrix derivative. -/
theorem freeDiagonalCandidate_hasDerivAt_11 (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => freeDiagonalCandidate z t 1 1)
      ((freeZeroCoefficientCandidate z * freeDiagonalCandidate z x) 1 1) x := by
  have h := ((hasDerivAt_id' x).smul_const (Complex.I * z)).cexp
  apply h.congr_deriv
  simp [freeZeroCoefficientCandidate, freeDiagonalCandidate,
    Matrix.diagonal_mul_diagonal, mul_comm]

end NlsGge.SpectralFoundations

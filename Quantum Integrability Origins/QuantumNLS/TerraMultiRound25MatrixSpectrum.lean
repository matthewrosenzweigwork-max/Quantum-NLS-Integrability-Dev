import QuantumNLS.TerraMultiRound22ResetMatrix

/-! Algebraic multiplicities of the symmetric two by two matrix. This is a
finite-dimensional ingredient, not the operator spectral correspondence. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace QuantumNLS.TerraMultiRound25MatrixSpectrum

/-- The characteristic polynomial factors with both roots counted. -/
theorem charpoly_factor (a : ℝ) (b : ℂ) :
    (Matrix.of ![![(a : ℂ), conj b], ![b, (a : ℂ)]]).charpoly =
      (X - C ((a + ‖b‖ : ℝ) : ℂ)) * (X - C ((a - ‖b‖ : ℝ) : ℂ)) := by
  rw [Matrix.charpoly_fin_two]
  have hprod : conj b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.det_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hprod]
  push_cast
  simp only [map_add, map_sub, map_mul, map_pow]
  ring

/-- The multiset contains each displayed eigenvalue once; when they coincide,
that value occurs twice. -/
theorem charpoly_roots (a : ℝ) (b : ℂ) :
    (Matrix.of ![![(a : ℂ), conj b], ![b, (a : ℂ)]]).charpoly.roots =
      {((a + ‖b‖ : ℝ) : ℂ), ((a - ‖b‖ : ℝ) : ℂ)} := by
  rw [charpoly_factor, Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))]
  simp only [roots_X_sub_C, Multiset.singleton_add, Multiset.insert_eq_cons]

end QuantumNLS.TerraMultiRound25MatrixSpectrum
#print axioms QuantumNLS.TerraMultiRound25MatrixSpectrum.charpoly_factor
#print axioms QuantumNLS.TerraMultiRound25MatrixSpectrum.charpoly_roots

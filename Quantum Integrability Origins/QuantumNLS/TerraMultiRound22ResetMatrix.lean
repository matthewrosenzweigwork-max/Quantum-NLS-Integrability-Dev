import Mathlib

/-!
An algebraic fragment of LOCAL-003, spectral_reduction.tex:90-103.
The hypotheses below are the finite-dimensional Hermitian and antiunitary
symmetry relations from the proof at line 106.  This fragment does not claim
that the source's contour-defined B satisfies them, nor does it claim the
analytic and uniform estimates of LOCAL-003.
-/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace QuantumNLS.TerraMultiRound22ResetMatrix

/-- A Hermitian matrix whose diagonal entries are exchanged by the source's
antiunitary symmetry. -/
theorem reset_matrix_consequences (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hdiagreal : M 0 0 = conj (M 0 0))
    (hdiagswap : M 0 0 = conj (M 1 1))
    (hoff : M 0 1 = conj (M 1 0)) :
    ∃ (a : ℝ) (b : ℂ),
      M = !![(a : ℂ), conj b; b, (a : ℂ)] ∧
      (∀ t : ℝ, (M - (t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 ↔
        t = a + ‖b‖ ∨ t = a - ‖b‖) ∧
      (a + ‖b‖ = a - ‖b‖ ↔ b = 0) := by
  let a : ℝ := (M 0 0).re
  let b : ℂ := M 1 0
  have him : (M 0 0).im = 0 := by
    have h := congrArg Complex.im hdiagreal
    simp only [Complex.conj_im] at h
    linarith
  have h00 : M 0 0 = (a : ℂ) := by
    apply Complex.ext <;> simp [a, him]
  have h11 : M 1 1 = (a : ℂ) := by
    have h := congrArg (starRingEnd ℂ) hdiagswap
    simpa [h00] using h.symm
  have hM : M = !![(a : ℂ), conj b; b, (a : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, hoff, b]
  refine ⟨a, b, hM, ?_, ?_⟩
  · intro t
    rw [hM, Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    norm_num
    have hprod : conj b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rw [hprod]
    have heq : (((a : ℂ) - t) * ((a : ℂ) - t) - (‖b‖ ^ 2 : ℝ)) =
        (((a - t) ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.ofReal_eq_zero]
    constructor
    · intro h
      have hf : (t - (a + ‖b‖)) * (t - (a - ‖b‖)) = 0 := by nlinarith
      rcases mul_eq_zero.mp hf with h | h
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> rw [h] <;> ring
  · constructor
    · intro h
      have : ‖b‖ = 0 := by linarith
      exact norm_eq_zero.mp this
    · intro h
      simp [h]

end QuantumNLS.TerraMultiRound22ResetMatrix
#print axioms QuantumNLS.TerraMultiRound22ResetMatrix.reset_matrix_consequences

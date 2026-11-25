import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

/-- The maximum of the four scalar entry norms. This avoids choosing a matrix
operator norm while controlling the actual finite-dimensional ZS recursion. -/
def actualComplexMatrixEntrySup (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  max (max ‖A 0 0‖ ‖A 0 1‖) (max ‖A 1 0‖ ‖A 1 1‖)

theorem norm_entry_le_actualComplexMatrixEntrySup
    (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ‖A i j‖ ≤ actualComplexMatrixEntrySup A := by
  unfold actualComplexMatrixEntrySup
  fin_cases i <;> fin_cases j
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem actualComplexMatrixEntrySup_mul_le
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    actualComplexMatrixEntrySup (A * B) ≤
      2 * actualComplexMatrixEntrySup A * actualComplexMatrixEntrySup B := by
  have hentryA (i j : Fin 2) : ‖A i j‖ ≤ actualComplexMatrixEntrySup A :=
    norm_entry_le_actualComplexMatrixEntrySup A i j
  have hentryB (i j : Fin 2) : ‖B i j‖ ≤ actualComplexMatrixEntrySup B :=
    norm_entry_le_actualComplexMatrixEntrySup B i j
  have hsupA_nonneg : 0 ≤ actualComplexMatrixEntrySup A :=
    le_trans (norm_nonneg _) (hentryA 0 0)
  have hprod (i j : Fin 2) :
      ‖(A * B) i j‖ ≤
        2 * actualComplexMatrixEntrySup A * actualComplexMatrixEntrySup B := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    calc
      ‖A i 0 * B 0 j + A i 1 * B 1 j‖ ≤
          ‖A i 0 * B 0 j‖ + ‖A i 1 * B 1 j‖ := norm_add_le _ _
      _ = ‖A i 0‖ * ‖B 0 j‖ + ‖A i 1‖ * ‖B 1 j‖ := by simp only [norm_mul]
      _ ≤ actualComplexMatrixEntrySup A * actualComplexMatrixEntrySup B +
          actualComplexMatrixEntrySup A * actualComplexMatrixEntrySup B := by
        apply add_le_add
        · exact mul_le_mul (hentryA i 0) (hentryB 0 j) (norm_nonneg _) hsupA_nonneg
        · exact mul_le_mul (hentryA i 1) (hentryB 1 j) (norm_nonneg _) hsupA_nonneg
      _ = 2 * actualComplexMatrixEntrySup A * actualComplexMatrixEntrySup B := by ring
  unfold actualComplexMatrixEntrySup
  apply max_le
  · apply max_le <;> exact hprod _ _
  · apply max_le <;> exact hprod _ _

end NlsGge.SpectralFoundations

end

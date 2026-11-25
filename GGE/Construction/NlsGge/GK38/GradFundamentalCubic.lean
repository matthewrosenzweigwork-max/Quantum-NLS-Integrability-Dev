import NlsGge.GK38.GradFundamentalFree

/-! # K1: finite matrix bounds for the cubic gradient kernels.
GK Chapter I, Lemma4.3. These are elementwise sup-norm estimates; the final
vector mass retains both scalar components explicitly.
-/
set_option autoImplicit false
open scoped Matrix.Norms.Elementwise
namespace NlsGge.GK38
noncomputable section

theorem k1MatrixMulNorm38 (A B : PairMat38) : ‖A * B‖ ≤ 2 * ‖A‖ * ‖B‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  calc
    _ ≤ ‖A i 0 * B 0 j‖ + ‖A i 1 * B 1 j‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖B‖ + ‖A‖ * ‖B‖ := by
      simp only [norm_mul]
      exact add_le_add
        (mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
          (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
          (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

theorem k1MatrixTripleNorm38 (A B C : PairMat38) : ‖A * B * C‖ ≤ 4 * ‖A‖ * ‖B‖ * ‖C‖ := by
  calc
    _ ≤ 2 * ‖A * B‖ * ‖C‖ := k1MatrixMulNorm38 _ _
    _ ≤ 2 * (2 * ‖A‖ * ‖B‖) * ‖C‖ := by gcongr; exact k1MatrixMulNorm38 _ _
    _ = _ := by ring

theorem k1AdjugateNorm38 (A : PairMat38) : ‖A.adjugate‖ ≤ ‖A‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg A)).mpr
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.adjugate_fin_two] <;>
    simp <;> exact Matrix.norm_entry_le_entrywise_sup_norm A

theorem k1AdjugateSub38 (A B : PairMat38) : (A - B).adjugate = A.adjugate - B.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two] <;> ring

theorem k1SwapNorm38 (A : PairMat38) : ‖k1SwapMat38 * A‖ ≤ ‖A‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg A)).mpr
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k1SwapMat38, Matrix.mul_apply, Fin.sum_univ_two] <;>
    exact Matrix.norm_entry_le_entrywise_sup_norm A

/-- Finite telescoping of three arbitrary matrices, with a common factor bound. -/
theorem k1MatrixTripleError38 (A B C a b c : PairMat38) (H : ℝ) (hH : 0 ≤ H)
    (hB : ‖B‖ ≤ H) (hC : ‖C‖ ≤ H) (ha : ‖a‖ ≤ H) (hb : ‖b‖ ≤ H) :
    ‖A * B * C - a * b * c‖ ≤
      4 * H ^ 2 * (‖A - a‖ + ‖B - b‖ + ‖C - c‖) := by
  have he : A * B * C - a * b * c =
      (A - a) * B * C + a * (B - b) * C + a * b * (C - c) := by noncomm_ring
  rw [he]
  have ht1 : ‖(A - a) * B * C‖ ≤ 4 * H ^ 2 * ‖A - a‖ := by
    calc
      _ ≤ 4 * ‖A - a‖ * ‖B‖ * ‖C‖ := k1MatrixTripleNorm38 _ _ _
      _ ≤ 4 * ‖A - a‖ * H * H := by gcongr
      _ = _ := by ring
  have ht2 : ‖a * (B - b) * C‖ ≤ 4 * H ^ 2 * ‖B - b‖ := by
    calc
      _ ≤ 4 * ‖a‖ * ‖B - b‖ * ‖C‖ := k1MatrixTripleNorm38 _ _ _
      _ ≤ 4 * H * ‖B - b‖ * H := by gcongr
      _ = _ := by ring
  have ht3 : ‖a * b * (C - c)‖ ≤ 4 * H ^ 2 * ‖C - c‖ := by
    calc
      _ ≤ 4 * ‖a‖ * ‖b‖ * ‖C - c‖ := k1MatrixTripleNorm38 _ _ _
      _ ≤ 4 * H * H * ‖C - c‖ := by gcongr
      _ = _ := by ring
  calc
    _ ≤ (‖(A - a) * B * C‖ + ‖a * (B - b) * C‖) + ‖a * b * (C - c)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (4 * H ^ 2 * ‖A - a‖ + 4 * H ^ 2 * ‖B - b‖) +
        4 * H ^ 2 * ‖C - c‖ := add_le_add (add_le_add ht1 ht2) ht3
    _ = _ := by ring

end
end NlsGge.GK38

import NlsGge.GK38.PairAnalyticDet
import NlsGge.GK38.PairAsymptoticsSeq
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # S3: singular-matrix control of a free diagonal

The independently reviewed direct matrix route for book Proposition 6.7.
The norm is the accepted elementwise maximum, not an operator norm. -/
set_option autoImplicit false
open scoped Matrix.Norms.Elementwise
namespace NlsGge.GK38
noncomputable section

/-- A two-entry kernel row, divided only after proving its chosen coordinate nonzero. -/
theorem kernel_row_free_bound38 (a b e σ x y : ℂ)
    (hx : x ≠ 0) (hy : ‖y‖ ≤ ‖x‖) (hrow : (a - σ) * x + b * y = 0) :
    ‖e - σ‖ ≤ ‖a - e‖ + ‖b‖ := by
  have he : (e - σ) * x = -((a - e) * x) - b * y := by
    linear_combination hrow
  have h := norm_add_le (-((a - e) * x)) (-(b * y))
  have hle : ‖e - σ‖ * ‖x‖ ≤ (‖a - e‖ + ‖b‖) * ‖x‖ := by
    calc _ = ‖(e - σ) * x‖ := (norm_mul _ _).symm
      _ = ‖-((a - e) * x) + -(b * y)‖ := by rw [he, sub_eq_add_neg]
      _ ≤ ‖-((a - e) * x)‖ + ‖-(b * y)‖ := h
      _ = ‖a - e‖ * ‖x‖ + ‖b‖ * ‖y‖ := by simp
      _ ≤ ‖a - e‖ * ‖x‖ + ‖b‖ * ‖x‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hy (norm_nonneg b))
      _ = _ := by ring
  exact le_of_mul_le_mul_right hle (norm_pos_iff.mpr hx)

/-- A maximal kernel-vector coordinate controls one of the free diagonal distances. -/
theorem matrix_kernel_free_diagonal38 (M : Matrix (Fin 2) (Fin 2) ℂ) (z σ : ℂ)
    (hdet : (M - σ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0) :
    ∃ i : Fin 2, ‖freeE z 1 i i - σ‖ ≤ 2 * ‖M - freeE z 1‖ := by
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hzero : ¬ (v 0 = 0 ∧ v 1 = 0) := by
    intro h
    apply hv
    ext i
    fin_cases i <;> simp [h.1, h.2]
  have hrow₀ : (M 0 0 - σ) * v 0 + M 0 1 * v 1 = 0 := by
    have h := congrArg (fun w => w 0) hker
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply] using h
  have hrow₁ : (M 1 1 - σ) * v 1 + M 1 0 * v 0 = 0 := by
    have h := congrArg (fun w => w 1) hker
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, add_comm] using h
  by_cases hmax : ‖v 1‖ ≤ ‖v 0‖
  · have hx : v 0 ≠ 0 := by
      intro hz
      have hh : v 1 = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hz] using hmax) (norm_nonneg _))
      exact hzero ⟨hz, hh⟩
    refine ⟨0, (kernel_row_free_bound38 (M 0 0) (M 0 1) (freeE z 1 0 0) σ
      (v 0) (v 1) hx hmax hrow₀).trans ?_⟩
    have hd := Matrix.norm_entry_le_entrywise_sup_norm (M - freeE z 1) (i := 0) (j := 0)
    have ho := Matrix.norm_entry_le_entrywise_sup_norm (M - freeE z 1) (i := 0) (j := 1)
    simp only [Matrix.sub_apply] at hd
    simp only [Matrix.sub_apply, show freeE z 1 0 1 = 0 from by simp [freeE], sub_zero] at ho
    linarith
  · have hm : ‖v 0‖ ≤ ‖v 1‖ := (lt_of_not_ge hmax).le
    have hx : v 1 ≠ 0 := by
      intro hz
      have hh : v 0 = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hz] using hm) (norm_nonneg _))
      exact hzero ⟨hh, hz⟩
    refine ⟨1, (kernel_row_free_bound38 (M 1 1) (M 1 0) (freeE z 1 1 1) σ
      (v 1) (v 0) hx hm hrow₁).trans ?_⟩
    have hd := Matrix.norm_entry_le_entrywise_sup_norm (M - freeE z 1) (i := 1) (j := 1)
    have ho := Matrix.norm_entry_le_entrywise_sup_norm (M - freeE z 1) (i := 1) (j := 0)
    simp only [Matrix.sub_apply] at hd
    simp only [Matrix.sub_apply, show freeE z 1 1 0 = 0 from by simp [freeE], sub_zero] at ho
    linarith

end
end NlsGge.GK38

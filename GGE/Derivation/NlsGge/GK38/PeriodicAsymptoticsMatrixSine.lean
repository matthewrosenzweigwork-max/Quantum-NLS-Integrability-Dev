import NlsGge.GK38.PeriodicAsymptoticsMatrix
import NlsGge.GK38.PairRealBridge

/-! # S3: determinant-one characteristic roots control the sine

Both possible trace signs are retained. Exponential nonvanishing precedes
cancellation; the proof never selects a spectral parity or a diagonalization. -/
set_option autoImplicit false
open scoped Matrix.Norms.Elementwise
namespace NlsGge.GK38
noncomputable section

/-- The sine factorization at either free diagonal, with the denominator cleared. -/
theorem free_diagonal_sine_factor38 (z σ : ℂ) (hσ : σ ^ 2 = 1) (i : Fin 2) :
    2 * ‖freeE z 1 i i‖ * ‖Complex.sin z‖ =
      ‖freeE z 1 i i - σ‖ * ‖freeE z 1 i i + σ‖ := by
  have hs : Complex.sin z = (freeE z 1 0 0 - freeE z 1 1 1) * Complex.I / 2 := by
    simp [freeE, Complex.sin, mul_comm]
  have hp := freeE_diag_prod z 1
  fin_cases i
  · have he : 2 * freeE z 1 0 0 * Complex.sin z =
        (freeE z 1 0 0 - σ) * (freeE z 1 0 0 + σ) * Complex.I := by
      rw [hs]
      linear_combination Complex.I * hσ - Complex.I * hp
    have hn := congrArg norm he
    simpa [norm_mul, Complex.norm_two, Complex.norm_I, freeE] using hn
  · have he : 2 * freeE z 1 1 1 * Complex.sin z =
        -((freeE z 1 1 1 - σ) * (freeE z 1 1 1 + σ) * Complex.I) := by
      rw [hs]
      linear_combination Complex.I * hp - Complex.I * hσ
    have hn := congrArg norm he
    simpa [norm_mul, Complex.norm_two, norm_neg, Complex.norm_I, freeE] using hn

/-- Uniform exponential bounds for each free diagonal and its reciprocal. -/
theorem free_diagonal_norm_bounds38 (z : ℂ) (c : ℝ) (him : |z.im| ≤ c) (i : Fin 2) :
    0 < ‖freeE z 1 i i‖ ∧ ‖freeE z 1 i i‖ ≤ Real.exp c ∧
      1 ≤ Real.exp c * ‖freeE z 1 i i‖ := by
  have hlo : -c ≤ z.im := by linarith [neg_abs_le z.im]
  have hhi : z.im ≤ c := (le_abs_self _).trans him
  have hb (t : ℝ) (hl : -c ≤ t) (hu : t ≤ c) :
      0 < Real.exp t ∧ Real.exp t ≤ Real.exp c ∧ 1 ≤ Real.exp c * Real.exp t := by
    refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr hu, ?_⟩
    rw [← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  fin_cases i
  · simpa [freeE, Complex.norm_exp] using hb z.im hlo hhi
  · simpa [freeE, Complex.norm_exp] using hb (-z.im) (by linarith) (by linarith)

/-- The accepted elementwise matrix error controls sine at any det-one trace-square root. -/
theorem matrix_root_sine_le38 (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) (c : ℝ)
    (_hc : 0 ≤ c) (him : |z.im| ≤ c) (hdet : M.det = 1)
    (htrace : (Matrix.trace M) ^ 2 = 4) :
    ‖Complex.sin z‖ ≤ Real.exp c * (Real.exp c + 1) * ‖M - freeE z 1‖ := by
  let σ : ℂ := Matrix.trace M / 2
  have hσ : σ ^ 2 = 1 := by dsimp [σ]; linear_combination (1 / 4 : ℂ) * htrace
  have hnorm : ‖σ‖ = 1 := by
    have hh := congrArg norm hσ
    rw [norm_pow, norm_one] at hh
    nlinarith [norm_nonneg σ]
  have hsing : (M - σ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
    rw [Matrix.det_fin_two] at hdet ⊢
    have ht : Matrix.trace M = M 0 0 + M 1 1 := by
      simp [Matrix.trace, Fin.sum_univ_two]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    norm_num
    dsimp [σ]
    rw [ht] at htrace ⊢
    linear_combination hdet - (1 / 4 : ℂ) * htrace
  obtain ⟨i, hi⟩ := matrix_kernel_free_diagonal38 M z σ hsing
  obtain ⟨hpos, hup, hinv⟩ := free_diagonal_norm_bounds38 z c him i
  have hsum : ‖freeE z 1 i i + σ‖ ≤ Real.exp c + 1 :=
    (norm_add_le _ _).trans (by rw [hnorm]; exact add_le_add hup le_rfl)
  have hfactor := free_diagonal_sine_factor38 z σ hσ i
  have hb : 2 * ‖freeE z 1 i i‖ * ‖Complex.sin z‖ ≤
      2 * ‖M - freeE z 1‖ * (Real.exp c + 1) := by
    rw [hfactor]
    exact mul_le_mul hi hsum (norm_nonneg _) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hb (Real.exp_pos c).le
  have hsin : 2 * ‖Complex.sin z‖ ≤
      Real.exp c * (2 * ‖M - freeE z 1‖ * (Real.exp c + 1)) := by
    have hh := mul_le_mul_of_nonneg_right hinv (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (norm_nonneg (Complex.sin z)))
    nlinarith
  nlinarith

/-- Concrete characteristic roots use the same full F5 matrix residual at time one. -/
theorem perChar_zero_sine_le38 (φ : PotPair) (z : ℂ) (c : ℝ)
    (hc : 0 ≤ c) (him : |z.im| ≤ c) (hzero : perChar φ z = 0) :
    ‖Complex.sin z‖ ≤ Real.exp c * (Real.exp c + 1) *
      ‖fundPair φ z ⟨1, zero_le_one, le_rfl⟩ - freeFund z ⟨1, zero_le_one, le_rfl⟩‖ := by
  have ht : (Matrix.trace (monodromyPair φ z)) ^ 2 = 4 := by
    change discrim φ z ^ 2 = 4
    change discrim φ z ^ 2 - 4 = 0 at hzero
    exact sub_eq_zero.mp hzero
  simpa only [monodromyPair_eq_fundPair, freeFund_apply] using
    matrix_root_sine_le38 (monodromyPair φ z) z c hc him (det_monodromyPair φ z) ht

end
end NlsGge.GK38

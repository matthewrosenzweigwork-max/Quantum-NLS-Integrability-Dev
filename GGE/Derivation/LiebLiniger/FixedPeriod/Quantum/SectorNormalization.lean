import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
Q-C supporting candidate, not checked by its author and not a sector implementation.
Source: LLFP-Q1-010,011. Mathlib pin: d13f23b723b8a846827a245b89c10fc7d3f11612.
The completed binary Hilbert tensor block below is genuine. It does not claim an
identification with Sym^n H: Q1-001, completed symmetric sectors and sector splitting
are missing. No conclusion is supplied as an assumption.
-/

noncomputable section
open scoped TensorProduct

namespace LLFPSectorCandidate

/-- The exact factorial coefficient of the source Wick-sector formula, with
    its prescribed zero branch when the input sector has too few particles. -/
def wickCoefficient (epsilon : ℝ) (p q n : ℕ) : ℝ :=
  if p ≤ n then
    epsilon ^ (((p : ℝ) + (q : ℝ)) / 2) *
      Real.sqrt ((n.factorial : ℝ) * ((n + q - p).factorial : ℝ)) /
        ((n - p).factorial : ℝ)
  else 0

theorem factorial_ratio_eq_falling (p q n : ℕ) (hn : p ≤ n) :
    Real.sqrt ((n.factorial : ℝ) * ((n + q - p).factorial : ℝ)) /
        ((n - p).factorial : ℝ) =
      Real.sqrt ((n.descFactorial p : ℝ) * ((n + q - p).descFactorial q : ℝ)) := by
  have hq : q ≤ n + q - p := by omega
  have hsub : n + q - p - q = n - p := by omega
  have h₁ : (n.factorial : ℝ) =
      ((n - p).factorial : ℝ) * (n.descFactorial p : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hn).symm
  have h₂ : ((n + q - p).factorial : ℝ) =
      ((n - p).factorial : ℝ) * ((n + q - p).descFactorial q : ℝ) := by
    have h := Nat.factorial_mul_descFactorial hq
    rw [hsub] at h
    exact_mod_cast h.symm
  have hd : ((n - p).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - p)
  calc
    _ = Real.sqrt (((n - p).factorial : ℝ) ^ 2 *
        ((n.descFactorial p : ℝ) * ((n + q - p).descFactorial q : ℝ))) /
        ((n - p).factorial : ℝ) := by rw [h₁, h₂]; congr 2; ring
    _ = (((n - p).factorial : ℝ) *
        Real.sqrt ((n.descFactorial p : ℝ) * ((n + q - p).descFactorial q : ℝ))) /
        ((n - p).factorial : ℝ) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
    _ = _ := by field_simp

theorem wickCoefficient_eq_falling (epsilon : ℝ) (p q n : ℕ) (hn : p ≤ n) :
    wickCoefficient epsilon p q n =
      epsilon ^ (((p : ℝ) + (q : ℝ)) / 2) *
        Real.sqrt ((n.descFactorial p : ℝ) * ((n + q - p).descFactorial q : ℝ)) := by
  unfold wickCoefficient
  rw [if_pos hn, mul_div_assoc, factorial_ratio_eq_falling p q n hn]

theorem wickCoefficient_nonneg (epsilon : ℝ) (p q n : ℕ) (he : 0 ≤ epsilon) :
    0 ≤ wickCoefficient epsilon p q n := by
  unfold wickCoefficient
  split_ifs
  · exact div_nonneg (mul_nonneg (Real.rpow_nonneg he _) (Real.sqrt_nonneg _))
      (Nat.cast_nonneg _)
  · exact le_rfl

theorem wickCoefficient_number (epsilon : ℝ) (r n : ℕ) (hn : r ≤ n) :
    wickCoefficient epsilon r r n = epsilon ^ r * (n.descFactorial r : ℝ) := by
  rw [wickCoefficient_eq_falling epsilon r r n hn, Nat.add_sub_cancel]
  have hdegree : ((r : ℝ) + (r : ℝ)) / 2 = (r : ℝ) := by ring
  rw [hdegree, Real.rpow_natCast, Real.sqrt_mul_self (Nat.cast_nonneg _)]

theorem scaled_falling_le_power (epsilon : ℝ) (r n : ℕ) (he : 0 ≤ epsilon) :
    epsilon ^ r * (n.descFactorial r : ℝ) ≤ (epsilon * (n : ℝ)) ^ r := by
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg he _)
  exact_mod_cast Nat.descFactorial_le_pow n r

/-- The Hilbert completion of the algebraic tensor with its canonical inner product. -/
abbrev HilbertTensor (E G : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] :=
  UniformSpace.Completion (E ⊗[ℂ] G)

section CompletionBound
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem norm_completion_le (f : E →L[ℂ] F) : ‖f.completion‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_le f.completion.continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro y
  simpa only [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe]
    using f.le_opNorm y
end CompletionBound

section TensorBlock
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- The source scalar times A tensor identity on the genuine completed tensor block.
    Identifying this with a Wick sector still requires the symmetric-sector maps. -/
def wickRawTensorBlock (epsilon : ℝ) (p q n : ℕ) (A : E →L[ℂ] F) :
    HilbertTensor E G →L[ℂ] HilbertTensor F G :=
  (wickCoefficient epsilon p q n : ℂ) • (A.rTensor G).completion

theorem wickRawTensorBlock_norm_le_coefficient (epsilon : ℝ) (p q n : ℕ)
    (A : E →L[ℂ] F) (he : 0 ≤ epsilon) :
    ‖wickRawTensorBlock (G := G) epsilon p q n A‖ ≤
      wickCoefficient epsilon p q n * ‖A‖ := by
  unfold wickRawTensorBlock
  have hc : 0 ≤ wickCoefficient epsilon p q n := wickCoefficient_nonneg epsilon p q n he
  calc
    _ ≤ ‖(wickCoefficient epsilon p q n : ℂ)‖ * ‖(A.rTensor G).completion‖ :=
      ContinuousLinearMap.opNorm_smul_le (wickCoefficient epsilon p q n : ℂ)
        (A.rTensor G).completion
    _ = wickCoefficient epsilon p q n * ‖(A.rTensor G).completion‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ wickCoefficient epsilon p q n * ‖A‖ :=
      mul_le_mul_of_nonneg_left
        ((norm_completion_le _).trans (ContinuousLinearMap.norm_rTensor_le G A)) hc

theorem wickRawTensorBlock_norm_le (epsilon : ℝ) (p q n : ℕ)
    (A : E →L[ℂ] F) (he : 0 < epsilon) (hn : p ≤ n) :
    ‖wickRawTensorBlock (G := G) epsilon p q n A‖ ≤
      epsilon ^ (((p : ℝ) + (q : ℝ)) / 2) *
        Real.sqrt ((n.descFactorial p : ℝ) * ((n + q - p).descFactorial q : ℝ)) * ‖A‖ := by
  simpa only [wickCoefficient_eq_falling epsilon p q n hn] using
    wickRawTensorBlock_norm_le_coefficient (G := G) epsilon p q n A he.le

theorem wickRawTensorBlock_eq_zero (epsilon : ℝ) (p q n : ℕ)
    (A : E →L[ℂ] F) (hn : n < p) :
    wickRawTensorBlock (G := G) epsilon p q n A = 0 := by
  simp only [wickRawTensorBlock, wickCoefficient, if_neg (Nat.not_le.mpr hn),
    Complex.ofReal_zero, zero_smul]

theorem wickRawNumber_norm_le (epsilon : ℝ) (r n : ℕ)
    (A : E →L[ℂ] E) (he : 0 < epsilon) :
    ‖wickRawTensorBlock (G := G) epsilon r r n A‖ ≤
      epsilon ^ r * (n.descFactorial r : ℝ) * ‖A‖ ∧
    epsilon ^ r * (n.descFactorial r : ℝ) * ‖A‖ ≤
      (epsilon * (n : ℝ)) ^ r * ‖A‖ := by
  constructor
  · by_cases hn : r ≤ n
    · simpa only [wickCoefficient_number epsilon r n hn] using
        wickRawTensorBlock_norm_le_coefficient (G := G) epsilon r r n A he.le
    · have hlt : n < r := Nat.lt_of_not_ge hn
      simp only [wickRawTensorBlock_eq_zero epsilon r r n A hlt, ContinuousLinearMap.opNorm_zero,
        Nat.descFactorial_of_lt hlt, Nat.cast_zero, mul_zero, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_right (scaled_falling_le_power epsilon r n he.le)
      (norm_nonneg _)
end TensorBlock

end LLFPSectorCandidate

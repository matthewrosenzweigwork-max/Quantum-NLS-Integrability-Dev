import NlsGge.Analysis.IntegerTails

set_option autoImplicit false
noncomputable section
namespace NlsGge.Analysis

/-- Retains p=0 as weight1; this reciprocal weight is used for actual H1 Fourier embedding. -/
theorem reciprocal_bracket_square_le (p : ℤ) :
    1 / (1 + (p : ℝ) ^ 2) ≤ (if p = 0 then 1 else 0) + inverseSquare p := by
  by_cases hp : p = 0
  · subst p
    simp
  · simp only [if_neg hp, zero_add]
    unfold inverseSquare
    have hcast : (p : ℝ) ≠ 0 := by exact_mod_cast hp
    have hsq : 0 < (p : ℝ) ^ 2 := sq_pos_of_ne_zero hcast
    exact one_div_le_one_div_of_le hsq (by nlinarith)

theorem summable_reciprocal_bracket_square :
    Summable (fun p : ℤ => 1 / (1 + (p : ℝ) ^ 2)) := by
  have hd : Summable (fun p : ℤ => if p = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  exact Summable.of_nonneg_of_le (fun p => by positivity)
    reciprocal_bracket_square_le (hd.add summable_inverseSquare)

theorem reciprocal_bracket_square_tsum_bound :
    (∑' p : ℤ, 1 / (1 + (p : ℝ) ^ 2)) ≤ 1 + inverseSquareTotal := by
  have hd : Summable (fun p : ℤ => if p = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  calc
    _ ≤ ∑' p : ℤ, ((if p = 0 then (1 : ℝ) else 0) + inverseSquare p) :=
      Summable.tsum_le_tsum reciprocal_bracket_square_le
        summable_reciprocal_bracket_square (hd.add summable_inverseSquare)
    _ = 1 + inverseSquareTotal := by
      rw [hd.tsum_add summable_inverseSquare, (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).tsum_eq]
      rfl

end NlsGge.Analysis

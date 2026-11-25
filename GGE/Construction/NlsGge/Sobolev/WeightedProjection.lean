import NlsGge.Sobolev.WeightedHilbert

set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators

namespace NlsGge.Pilot

variable (w : ℤ → ℝ) [hw : Fact (∀ n : ℤ, 0 < w n)]

def weightedProjectionLinear (s : Finset ℤ) : WeightedHilbert w →ₗ[ℂ] WeightedHilbert w where
  toFun := weightedProjection w s
  map_add' x y := by
    apply Subtype.ext
    funext n
    change (weightedProjection w s (x + y) : ℤ → ℂ) n =
      (weightedProjection w s x : ℤ → ℂ) n + (weightedProjection w s y : ℤ → ℂ) n
    simp only [weightedProjection_apply]
    by_cases hn : n ∈ s
    · simp only [if_pos hn]
      rfl
    · simp only [if_neg hn, add_zero]
  map_smul' c x := by
    apply Subtype.ext
    funext n
    change (weightedProjection w s (c • x) : ℤ → ℂ) n =
      c • (weightedProjection w s x : ℤ → ℂ) n
    simp only [weightedProjection_apply]
    by_cases hn : n ∈ s
    · simp only [if_pos hn]
      rfl
    · simp only [if_neg hn, smul_zero]

theorem weightedProjection_norm_le (s : Finset ℤ) (x : WeightedHilbert w) :
    ‖weightedProjection w s x‖ ≤ ‖x‖ := by
  have hsq : ‖weightedProjection w s x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [weightedHilbert_norm_sq w, weightedHilbert_norm_sq w]
    apply Summable.tsum_le_tsum (fun n => ?_)
      (weightedHilbert_hasSum w (weightedProjection w s x)).summable
      (weightedHilbert_hasSum w x).summable
    rw [weightedProjection_apply]
    by_cases hn : n ∈ s
    · simp only [if_pos hn, le_refl]
    · simp only [if_neg hn, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      exact mul_nonneg (hw.out n).le (sq_nonneg _)
  nlinarith [norm_nonneg x, norm_nonneg (weightedProjection w s x)]

def weightedProjectionContinuous (s : Finset ℤ) : WeightedHilbert w →L[ℂ] WeightedHilbert w :=
  (weightedProjectionLinear w s).mkContinuous 1
    (fun x => by
      change ‖weightedProjection w s x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using weightedProjection_norm_le w s x)

theorem weightedProjectionContinuous_apply (s : Finset ℤ) (x : WeightedHilbert w) :
    weightedProjectionContinuous w s x = weightedProjection w s x := rfl

theorem weightedProjection_idempotent (s : Finset ℤ) (x : WeightedHilbert w) :
    weightedProjection w s (weightedProjection w s x) = weightedProjection w s x := by
  apply Subtype.ext
  funext n
  by_cases hn : n ∈ s <;> simp [weightedProjection_apply, hn]

theorem weightedProjection_range_residual (s : Finset ℤ) (x y : WeightedHilbert w) :
    inner ℂ (weightedProjection w s y) (x - weightedProjection w s x) = 0 := by
  rw [← (weightedIsometry w).inner_map_map, lp.inner_eq_tsum]
  have hzero (n : ℤ) :
      inner ℂ (weightedIsometry w (weightedProjection w s y) n)
        (weightedIsometry w (x - weightedProjection w s x) n) = 0 := by
    change inner ℂ
      ((Real.sqrt (w n) : ℂ) * (weightedProjection w s y : ℤ → ℂ) n)
      ((Real.sqrt (w n) : ℂ) * ((x : ℤ → ℂ) n -
        (weightedProjection w s x : ℤ → ℂ) n)) = 0
    rw [weightedProjection_apply, weightedProjection_apply]
    by_cases hn : n ∈ s <;> simp [hn]
  exact (tsum_congr hzero).trans tsum_zero

end NlsGge.Pilot

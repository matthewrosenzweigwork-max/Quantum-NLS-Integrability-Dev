import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Sobolev.WeightedProjection

set_option autoImplicit false
set_option pp.maxSteps 10000000
noncomputable section
open scoped BigOperators

namespace NlsGge.Pilot.WeightedProjectionFiniteHeadBoxNormBoundV2

variable (w : ℤ → ℝ) [Fact (∀ n : ℤ, 0 < w n)]

/-- A coordinatewise radius-r box on a finite set controls the Hilbert norm
of the difference of the corresponding finite weighted projections. -/
lemma weightedProjection_diff_norm_sq_le
    (S : Finset ℤ) (x y : WeightedHilbert w) (r : ℝ) (hr : 0 < r)
    (hbox : ∀ n ∈ S, ‖(x : ℤ → ℂ) n - (y : ℤ → ℂ) n‖ < r) :
    ‖weightedProjection w S x - weightedProjection w S y‖ ^ 2 ≤
      r ^ 2 * ∑ n ∈ S, w n := by
  have hcoord (n : ℤ) :
      (weightedProjection w S x - weightedProjection w S y : WeightedHilbert w) n =
        if n ∈ S then (x : ℤ → ℂ) n - (y : ℤ → ℂ) n else 0 := by
    by_cases hn : n ∈ S
    · change (weightedProjection w S x : ℤ → ℂ) n -
          (weightedProjection w S y : ℤ → ℂ) n = _
      simp [weightedProjection_apply, hn]
    · change (weightedProjection w S x : ℤ → ℂ) n -
          (weightedProjection w S y : ℤ → ℂ) n = _
      simp [weightedProjection_apply, hn]
  rw [weightedHilbert_norm_sq w]
  rw [tsum_eq_sum (s := S) (fun n hn => by simp [hcoord, hn])]
  have hfinite :
      (∑ n ∈ S, w n * ‖(weightedProjection w S x - weightedProjection w S y :
        WeightedHilbert w) n‖ ^ 2) =
        ∑ n ∈ S, w n * ‖(x : ℤ → ℂ) n - (y : ℤ → ℂ) n‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [hcoord, hn]
  rw [hfinite]
  calc
    (∑ n ∈ S, w n * ‖(x : ℤ → ℂ) n - (y : ℤ → ℂ) n‖ ^ 2) ≤
        ∑ n ∈ S, w n * r ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          have hcoord' := hbox n hn
          have hsq : ‖(x : ℤ → ℂ) n - (y : ℤ → ℂ) n‖ ^ 2 ≤ r ^ 2 := by
            nlinarith [norm_nonneg ((x : ℤ → ℂ) n - (y : ℤ → ℂ) n)]
          exact mul_le_mul_of_nonneg_left hsq
            ((show 0 < w n from (Fact.out : ∀ n : ℤ, 0 < w n) n).le)
    _ = r ^ 2 * ∑ n ∈ S, w n := by
          rw [← Finset.sum_mul]
          ring

#check @weightedProjection_diff_norm_sq_le

end NlsGge.Pilot.WeightedProjectionFiniteHeadBoxNormBoundV2

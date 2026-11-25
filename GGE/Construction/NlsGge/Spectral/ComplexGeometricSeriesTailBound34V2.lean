import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations

/-- Comparison first establishes summability, then controls the tail after
the actual zeroth term. This cannot assign an energy to a divergent tsum. -/
theorem complexGeometricSeriesTail_bound34
    (g : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A) (hA1 : A < 1)
    (hb : ∀ k : ℕ, ‖g k‖ ≤ A^k) :
    Summable g ∧ ‖(∑' k : ℕ, g k) - g 0‖ ≤ A/(1-A) := by
  have hs : Summable g := (summable_geometric_of_lt_one hA hA1).of_norm_bounded hb
  refine ⟨hs, ?_⟩
  have he : (∑' k : ℕ, g k) - g 0 = ∑' k : ℕ, g (k+1) := by
    rw [hs.tsum_eq_zero_add]
    abel
  rw [he]
  apply tsum_of_norm_bounded
  · simpa only [pow_succ', div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hA hA1).mul_left A
  · intro k
    simpa only [pow_succ'] using hb (k+1)

end NlsGge.SpectralFoundations
end

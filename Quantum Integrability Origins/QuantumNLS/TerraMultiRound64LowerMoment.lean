import QuantumNLS.TerraMultiRound60MomentComparison

/-! Lower even moments of a finite measure are finite whenever a higher one is. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound64LowerMoment

theorem even_integrable_of_higher (μ : Measure ℝ) [IsFiniteMeasure μ] (p q : ℕ) (hpq : p ≤ q)
    (hq : Integrable (fun t : ℝ => t^(2*q)) μ) : Integrable (fun t : ℝ => t^(2*p)) μ := by
  have he (n : ℕ) : (fun t : ℝ => ‖t‖^(2*n)) = (fun t : ℝ => t^(2*n)) := by
    funext t
    simp only [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg ((even_two_mul n).pow_nonneg t)]
  have hq' : Integrable (fun t : ℝ => ‖t‖^(2*q)) μ := by rw [he]; exact hq
  have hp' := integrable_norm_pow_of_le (μ := μ) (f := fun t : ℝ => t)
    measurable_id.aestronglyMeasurable (show 2*p ≤ 2*q by omega) hq'
  simpa only [he] using hp'

#print axioms even_integrable_of_higher
end QuantumNLS.TerraMultiRound64LowerMoment

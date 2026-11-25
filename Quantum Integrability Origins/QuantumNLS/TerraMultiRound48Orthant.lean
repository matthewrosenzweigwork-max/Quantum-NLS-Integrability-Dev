import QuantumNLS.TerraMultiRound47ShiftIntegrable
import Mathlib.MeasureTheory.Integral.Pi

/-! Exponential domination on a finite positive orthant. This supports the
integrability side of treewise Fubini; it does not assert the tree identity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound48Orthant

/-- The exponential product is integrable over any finite positive orthant. -/
theorem orthant_exp_integrable (n : ℕ) :
    Integrable (fun t : Fin n → ℝ => ∏ i, Real.exp (-t i))
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) := by
  exact Integrable.fintype_prod (fun _ => integrableOn_exp_neg_Ioi 0)

/-- A bounded continuous correlation has an integrable exponentially damped
orthant integrand. Its bound and continuity must be established separately. -/
theorem orthant_bounded_integrable (n : ℕ) (C : (Fin n → ℝ) → ℂ) (B : ℝ)
    (hC : Continuous C) (hb : ∀ t, ‖C t‖ ≤ B) :
    Integrable (fun t : Fin n → ℝ =>
      ((∏ i, Real.exp (-t i) : ℝ) : ℂ) * C t)
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) := by
  have hg := (orthant_exp_integrable n).const_mul B
  apply hg.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · apply Complex.continuous_ofReal.comp
      exact continuous_finsetProd _ (fun i _ => Real.continuous_exp.comp ((continuous_apply i).neg))
    · exact hC
  · filter_upwards with t
    have hp : 0 ≤ ∏ i : Fin n, Real.exp (-t i) := Finset.prod_nonneg (fun i hi => (Real.exp_pos _).le)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
    calc
      (∏ i : Fin n, Real.exp (-t i)) * ‖C t‖ ≤ (∏ i : Fin n, Real.exp (-t i)) * B := mul_le_mul_of_nonneg_left (hb t) hp
      _ = B * ∏ i : Fin n, Real.exp (-t i) := mul_comm _ _

#print axioms orthant_exp_integrable
#print axioms orthant_bounded_integrable
end QuantumNLS.TerraMultiRound48Orthant

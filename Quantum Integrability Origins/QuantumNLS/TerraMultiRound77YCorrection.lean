import QuantumNLS.TerraMultiRound77CorrectionIdentity

/-! The finite-moment correction identity in the printed Y variable. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Reg010LowBasic
open QuantumNLS.TerraMultiRound77CorrectionIdentity
namespace QuantumNLS.TerraMultiRound77YCorrection

/-- Change variables from the squared parameter to the printed Y integral.
The identity is valid for any correction function, including at nonintegrable
values under Lean's integral convention. -/
theorem correction_change_variable (s : ℝ) (F : ℝ → ℝ) :
    (∫ t in Ioi 0, t ^ (s-2) * F (Real.sqrt t)) =
      2 * ∫ Y in Ioi 0, Y ^ (2*s-3) * F Y := by
  have hchange := integral_comp_rpow_Ioi_of_pos
    (g := fun t : ℝ => t ^ (s-2) * F (Real.sqrt t)) (p := 2) (by norm_num)
  rw [← hchange, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro Y hY
  simp only [smul_eq_mul, Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.sqrt_sq (le_of_lt hY)]
  have hp : (Y ^ 2) ^ (s-2) = Y ^ (2*(s-2)) := by
    rw [Real.rpow_mul hY.le, Real.rpow_two]
  rw [hp]
  have h := Real.rpow_add hY 1 (2*(s-2))
  rw [Real.rpow_one] at h
  have he : 1 + 2*(s-2) = 2*s-3 := by ring
  rw [he] at h
  rw [h]
  ring

/-- Physical and free fractional moments differ by the actual correction
integral whenever both moments are finite. The positive normalizing constant
is explicit, while its sine evaluation is a separate obligation. -/
theorem physical_free_Y_correction {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : L2T L) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hμ : Integrable (fun x : ℝ => |x| ^ (2*s)) (PhysicalQuantumMeasure.measure hκ u))
    (hν : Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L u)) :
    (∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ u) -
      (∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L u) =
      (2 / (∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1)) *
        ∫ Y in Ioi 0, Y ^ (2*s-3) * correction κ hκ u Y := by
  have hp : s ∈ Ioo (0 : ℝ) 1 := ⟨hs0, hs1⟩
  have hC := Real.integral_rpowIntegrand₀₁_one_pos hp
  have h := physical_free_finite_correction hκ u s hs0 hs1 hμ hν
  rw [correction_change_variable] at h
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (ne_of_gt hC)).2
  nlinarith

#print axioms correction_change_variable
#print axioms physical_free_Y_correction
end QuantumNLS.TerraMultiRound77YCorrection

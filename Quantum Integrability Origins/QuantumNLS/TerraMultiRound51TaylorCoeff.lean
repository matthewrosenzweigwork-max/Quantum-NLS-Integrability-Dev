import QuantumNLS.TerraMultiRound49IntegratedLittleO

/-! Exponential integrability of each pathwise Taylor coefficient. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound51TaylorCoeff
open QuantumNLS.CorrelationTaylor QuantumNLS.TerraMultiRound48Leading
open QuantumNLS.TerraMultiRound48OrthantMoment QuantumNLS.TerraMultiRound49TaylorPath

/-- The unscaled coefficient of the Taylor polynomial on a path family. -/
def pathCoeff {n q : ℕ} (C : (Fin q → ℝ) → ℂ)
    (paths : Fin q → Finset (Fin n)) (j : ℕ) (t : Fin n → ℝ) : ℂ :=
  ((Nat.factorial j : ℝ)⁻¹) • iteratedFDeriv ℝ j C 0
    (fun _ : Fin j => scaledShift paths 1 t)

theorem pathCoeff_continuous {n q : ℕ} (C : (Fin q → ℝ) → ℂ)
    (paths : Fin q → Finset (Fin n)) (j : ℕ) : Continuous (pathCoeff C paths j) := by
  unfold pathCoeff
  exact (continuous_const : Continuous (fun _ : Fin n → ℝ => ((Nat.factorial j : ℝ)⁻¹))).smul ((iteratedFDeriv ℝ j C 0).cont.comp
    (continuous_pi (fun _ => scaledShift_continuous_t paths 1)))

/-- Every coefficient, including degree zero, has an integrable exponential
majorant on the finite orthant. No differentiability assumption is needed for
this integrability statement. -/
theorem pathCoeff_integrable {n q : ℕ} (C : (Fin q → ℝ) → ℂ)
    (paths : Fin q → Finset (Fin n)) (j : ℕ) :
    Integrable (fun t : Fin n → ℝ =>
      ((∏ i, Real.exp (-t i) : ℝ) : ℂ) * pathCoeff C paths j t)
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) := by
  let B : ℝ := ‖(Nat.factorial j : ℝ)⁻¹‖ * ‖iteratedFDeriv ℝ j C 0‖ * (q : ℝ) ^ j
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg := (orthant_sum_moment n j).const_mul B
  apply hg.mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · apply Complex.continuous_ofReal.comp
      exact continuous_finsetProd _ (fun i _ => Real.continuous_exp.comp ((continuous_apply i).neg))
    · exact pathCoeff_continuous C paths j
  · filter_upwards with t
    have hp : 0 ≤ ∏ i : Fin n, Real.exp (-t i) :=
      Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)
    have ht : 0 ≤ ∑ i : Fin n, |t i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hs : ‖scaledShift paths 1 t‖ ≤ (q : ℝ) * ∑ i, |t i| := by
      calc
        _ ≤ eucl (scaledShift paths 1 t) := norm_le_eucl _
        _ ≤ (q : ℝ) * (|1| * ∑ i, |t i|) := eucl_scaledShift_le paths 1 t
        _ = _ := by simp
    have hm : ‖iteratedFDeriv ℝ j C 0 (fun _ : Fin j => scaledShift paths 1 t)‖ ≤
        ‖iteratedFDeriv ℝ j C 0‖ * ((q : ℝ) * ∑ i, |t i|) ^ j := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ j C 0).le_opNorm_mul_prod_of_le (m := fun _ : Fin j => scaledShift paths 1 t) (b := fun _ => (q : ℝ) * ∑ i, |t i|) (fun _ => hs)
    have hc : ‖pathCoeff C paths j t‖ ≤ B * (∑ i, |t i|) ^ j := by
      unfold pathCoeff
      rw [norm_smul]
      calc
        _ ≤ ‖(Nat.factorial j : ℝ)⁻¹‖ * (‖iteratedFDeriv ℝ j C 0‖ * ((q : ℝ) * ∑ i, |t i|) ^ j) :=
          mul_le_mul_of_nonneg_left hm (norm_nonneg _)
        _ = _ := by dsimp [B]; rw [mul_pow]; ring
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
    calc
      _ ≤ (∏ i : Fin n, Real.exp (-t i)) * (B * (∑ i, |t i|) ^ j) :=
        mul_le_mul_of_nonneg_left hc hp
      _ = B * ((∏ i : Fin n, Real.exp (-t i)) * (∑ i, |t i|) ^ j) := by ring

#print axioms pathCoeff_continuous
#print axioms pathCoeff_integrable
end QuantumNLS.TerraMultiRound51TaylorCoeff

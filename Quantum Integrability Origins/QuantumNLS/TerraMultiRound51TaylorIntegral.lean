import QuantumNLS.TerraMultiRound51TaylorCoeff

/-! Finite orthant integration of the actual Taylor polynomial coefficients. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound51TaylorIntegral
open QuantumNLS.CorrelationTaylor QuantumNLS.TerraMultiRound48Leading
open QuantumNLS.TerraMultiRound49TaylorPath QuantumNLS.TerraMultiRound51TaylorCoeff

def integratedCoeff {n q : ℕ} (C : (Fin q → ℝ) → ℂ)
    (paths : Fin q → Finset (Fin n)) (j : ℕ) : ℂ :=
  ∫ t : Fin n → ℝ, ((∏ i, Real.exp (-t i) : ℝ) : ℂ) * pathCoeff C paths j t ∂
    (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ))))

theorem taylorPoly_path {n q : ℕ} (C : (Fin q → ℝ) → ℂ)
    (paths : Fin q → Finset (Fin n)) (d : ℕ) (z : ℝ) (t : Fin n → ℝ) :
    taylorPoly C d (scaledShift paths z t) =
      ∑ j ∈ Finset.range (d + 1), (z ^ j) • pathCoeff C paths j t := by
  unfold taylorPoly
  apply Finset.sum_congr rfl
  intro j hj
  rw [shift_eq_smul]
  rw [(iteratedFDeriv ℝ j C 0).map_smul_univ (fun _ => z)
    (fun _ => scaledShift paths 1 t)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pathCoeff, smul_smul]
  congr 1
  ring

/-- Integrating a finite Taylor polynomial gives its genuine finite list of
orthant integrals, with the scale power carried outside each integral. -/
theorem integral_taylorPoly_path {n q : ℕ} (C : (Fin q → ℝ) → ℂ)
    (paths : Fin q → Finset (Fin n)) (d : ℕ) (z : ℝ) :
    (∫ t : Fin n → ℝ, ((∏ i, Real.exp (-t i) : ℝ) : ℂ) *
      taylorPoly C d (scaledShift paths z t) ∂
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ))))) =
    ∑ j ∈ Finset.range (d + 1), (z ^ j) • integratedCoeff C paths j := by
  simp_rw [taylorPoly_path, Finset.mul_sum, mul_smul_comm]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact integral_smul _ _
  · intro j hj
    exact (pathCoeff_integrable C paths j).smul (z ^ j : ℝ)

#print axioms taylorPoly_path
#print axioms integral_taylorPoly_path
end QuantumNLS.TerraMultiRound51TaylorIntegral

import QuantumNLS.TerraMultiRound61FreeMeasure

/-! The actual free measure has the Fourier even moments, including infinity. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace QuantumNLS.TerraMultiRound62FreeMoments
open QuantumNLS.PhysicalTensor QuantumNLS.Fourier QuantumNLS.FreeLimit
open QuantumNLS.RootWeightedCellsR26
variable {L : ℝ} [Fact (0 < L)]

theorem free_extended_moment (u : L2T L) (s : ℕ) :
    (∫⁻ t : ℝ, ENNReal.ofReal (t^(2*s)) ∂(freeMeasure L u)) =
      ∑' n : ℤ, ENNReal.ofReal (‖coeff L (u : AddCircle L → ℂ) n‖ ^ 2) *
        ENNReal.ofReal ((momentum L n)^(2*s)) := by
  unfold freeMeasure
  rw [lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl

theorem free_finite_moment (u : L2T L) (s : ℕ)
    (h : Integrable (fun t : ℝ => t^(2*s)) (freeMeasure L u)) :
    (∫ t : ℝ, t^(2*s) ∂(freeMeasure L u)) =
      ∑' n : ℤ, (momentum L n)^(2*s) * ‖coeff L (u : AddCircle L → ℂ) n‖ ^ 2 := by
  change Integrable (fun t : ℝ => t^(2*s)) (Measure.sum (fun n : ℤ =>
    ENNReal.ofReal (‖coeff L (u : AddCircle L → ℂ) n‖ ^ 2) •
      Measure.dirac (2 * Real.pi * n / L))) at h
  have he := (hasSum_integral_measure h).tsum_eq.symm
  convert he using 1
  · rfl
  · apply tsum_congr
    intro n
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
    unfold momentum
    ring

#print axioms free_extended_moment
#print axioms free_finite_moment
end QuantumNLS.TerraMultiRound62FreeMoments

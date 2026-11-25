import QuantumNLS.TerraMultiRound61MomentRecurrence

/-! Difference of finite regularized moments, without subtracting infinities. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound61DifferenceRecurrence
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound61MomentRecurrence

theorem difference_recurrence (μ ν : Measure ℝ) (s : ℕ) (Y : ℝ) (hY : 0 < Y)
    (hμ : Integrable (fun t : ℝ => t ^ (2*s)) μ)
    (hν : Integrable (fun t : ℝ => t ^ (2*s)) ν) :
    (∫ t, kernel (s+1) Y t ∂μ) - (∫ t, kernel (s+1) Y t ∂ν) =
      Y^2 * ((∫ t : ℝ, t ^ (2*s) ∂μ) - (∫ t : ℝ, t ^ (2*s) ∂ν)) -
      Y^2 * ((∫ t, kernel s Y t ∂μ) - (∫ t, kernel s Y t ∂ν)) := by
  rw [integral_recurrence μ s Y hY hμ, integral_recurrence ν s Y hY hν]
  ring

#print axioms difference_recurrence
end QuantumNLS.TerraMultiRound61DifferenceRecurrence

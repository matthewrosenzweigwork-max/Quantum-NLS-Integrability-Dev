import QuantumNLS.TerraMultiRound61DifferenceRecurrence

/-! Every finite higher regularization is obtained by exact division. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound61FiniteDivision
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound61DifferenceRecurrence

def dividedDifference (μ ν : Measure ℝ) (Y : ℝ) : ℕ → ℝ
  | 0 => (∫ t, kernel 0 Y t ∂μ) - (∫ t, kernel 0 Y t ∂ν)
  | s+1 => Y^2 * ((∫ t : ℝ, t ^ (2*s) ∂μ) - (∫ t : ℝ, t ^ (2*s) ∂ν)) -
      Y^2 * dividedDifference μ ν Y s

theorem finite_division (μ ν : Measure ℝ) (Y : ℝ) (hY : 0 < Y) :
    ∀ s : ℕ,
      (∀ j < s, Integrable (fun t : ℝ => t ^ (2*j)) μ) →
      (∀ j < s, Integrable (fun t : ℝ => t ^ (2*j)) ν) →
      dividedDifference μ ν Y s =
        (∫ t, kernel s Y t ∂μ) - (∫ t, kernel s Y t ∂ν) := by
  intro s
  induction s with
  | zero => intros; rfl
  | succ s ih =>
    intro hμ hν
    have hμ' : ∀ j < s, Integrable (fun t : ℝ => t ^ (2*j)) μ := by
      intro j hj; exact hμ j (by omega)
    have hν' : ∀ j < s, Integrable (fun t : ℝ => t ^ (2*j)) ν := by
      intro j hj; exact hν j (by omega)
    rw [dividedDifference, ih hμ' hν']
    exact (difference_recurrence μ ν s Y hY (hμ s (by omega)) (hν s (by omega))).symm

#print axioms finite_division
end QuantumNLS.TerraMultiRound61FiniteDivision

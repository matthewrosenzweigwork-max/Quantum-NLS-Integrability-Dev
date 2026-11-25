import QuantumNLS.TerraMultiRound62LimitComparison

/-! Finiteness transfers both ways under a finite regularized-difference limit. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
namespace QuantumNLS.TerraMultiRound62MomentTransfer
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound62LimitComparison

theorem moment_transfer (μ ν : Measure ℝ) (s : ℕ) (r : ℝ)
    (hμlower : Integrable (fun t : ℝ => t^(2*s)) μ)
    (hνlower : Integrable (fun t : ℝ => t^(2*s)) ν)
    (hdiff : Tendsto (fun n : ℕ => (∫ t, kernel (s+1) ((n : ℝ)+1) t ∂μ) -
      (∫ t, kernel (s+1) ((n : ℝ)+1) t ∂ν)) atTop (𝓝 r)) :
    (Integrable (fun t : ℝ => t^(2*(s+1))) μ ↔
      Integrable (fun t : ℝ => t^(2*(s+1))) ν) ∧
    (Integrable (fun t : ℝ => t^(2*(s+1))) ν →
      (∫ t : ℝ, t^(2*(s+1)) ∂μ) = (∫ t : ℝ, t^(2*(s+1)) ∂ν) + r) := by
  have hswap : Tendsto (fun n : ℕ => (∫ t, kernel (s+1) ((n : ℝ)+1) t ∂ν) -
      (∫ t, kernel (s+1) ((n : ℝ)+1) t ∂μ)) atTop (𝓝 (-r)) := by
    simpa only [neg_sub] using hdiff.neg
  constructor
  · constructor
    · intro hμ
      exact (finite_of_difference ν μ s (-r) hνlower hμ hswap).1
    · intro hν
      exact (finite_of_difference μ ν s r hμlower hν hdiff).1
  · intro hν
    exact (finite_of_difference μ ν s r hμlower hν hdiff).2

#print axioms moment_transfer
end QuantumNLS.TerraMultiRound62MomentTransfer

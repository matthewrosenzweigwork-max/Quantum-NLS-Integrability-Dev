import QuantumNLS.TransferNormality
/-! integrator-authored trusted spec for R-198C12E2 basis:cor:transfer-normality (Terra r134 ACCEPT): frozen statements of TransferNormality restated verbatim. -/
namespace R198Spec
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open QuantumNLS QuantumNLS.TransferNormality

set_option maxHeartbeats 4000000 in
theorem transfer_normality_spec  (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :
    ∀ z w : ℂ,
      Commute (QuantumNLS.BethePhysicalTransfer.transfer L N c z)
        (QuantumNLS.BethePhysicalTransfer.transfer L N c w) ∧
      Commute (QuantumNLS.BethePhysicalTransfer.transfer L N c z)
        (ContinuousLinearMap.adjoint (QuantumNLS.BethePhysicalTransfer.transfer L N c w)) ∧
      Commute (ContinuousLinearMap.adjoint (QuantumNLS.BethePhysicalTransfer.transfer L N c z))
        (QuantumNLS.BethePhysicalTransfer.transfer L N c w) ∧
      Commute (ContinuousLinearMap.adjoint (QuantumNLS.BethePhysicalTransfer.transfer L N c z))
        (ContinuousLinearMap.adjoint (QuantumNLS.BethePhysicalTransfer.transfer L N c w)) := by
  apply QuantumNLS.TransferNormality.transfer_normality <;> assumption

end R198Spec
#print axioms R198Spec.transfer_normality_spec

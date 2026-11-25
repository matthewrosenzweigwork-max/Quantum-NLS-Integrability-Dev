/-
QuantumNLS.PlacementConsistency — physical and generic views of DEF-041.

Source: source-text/chapters/local/quantum_periods.tex:15–30.  This module
uses the bounded-kernel carrier and product-symbol results already proved in
KernelDefinition; it adds no parallel kernel or placement definition.
-/
import QuantumNLS.KernelDefinition

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.PhysicalTensor

noncomputable section

namespace QuantumNLS.PlacementConsistency

/-! ## The literal physical placement agrees with the generic kernel package -/

/-- The physical DEF-041 placement is the same operator as the arbitrary-total
kernel placement from `KernelDefinition`.  This records the consistency of
the physical `p + (N-p) = N` specialization with the bounded-kernel API. -/
theorem physicalU_N_r_eq_genericU_N_r (L : ℝ) [Fact (0 < L)]
    (N r : ℕ) (hr : r ≤ N)
    (A : QuantumNLS.KernelDefinition.BoundedSymmetricKernel
      (PhysicalTensor.L2T L) r) :
    QuantumNLS.KernelDefinition.physicalU_N_r L N r hr A =
      QuantumNLS.KernelDefinition.genericU_N_r
        (H := PhysicalTensor.L2T L) N r hr A := by
  unfold QuantumNLS.KernelDefinition.physicalU_N_r
    QuantumNLS.PhysicalPlacements.physicalQ_N_p
    QuantumNLS.PhysicalPlacements.castSymSectorOperator
    QuantumNLS.KernelDefinition.genericU_N_r
    QuantumNLS.KernelDefinition.castSymSectorOperator
  rw [← QuantumNLS.KernelDefinition.U_N_r_eq_Q_N_p]

end QuantumNLS.PlacementConsistency

#print axioms QuantumNLS.PlacementConsistency.physicalU_N_r_eq_genericU_N_r

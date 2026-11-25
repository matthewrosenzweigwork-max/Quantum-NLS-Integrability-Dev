import QuantumNLS.TerraMultiRound19ProductTerms
import QuantumNLS.RootOverlapLimit

/-! Additivity of concrete overlap placement kernels in both arguments. -/
set_option autoImplicit false
noncomputable section
open QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion QuantumNLS.PlacementProduct
open QuantumNLS.RootOverlapLimit
namespace QuantumNLS.TerraMultiRound20OverlapAdd

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rightPlacement_add {p q s : ℕ} {hsp : s ≤ p} {hsq : s ≤ q}
    (C : OverlapConfiguration p q s hsp hsq)
    (A B : BoundedSymmetricKernel H q) :
    rightPlacement C (A + B) = rightPlacement C A + rightPlacement C B := by
  unfold rightPlacement
  rw [subsetPlacement_add, castTensorOperator_add]

theorem fusion_add_left {p q s : ℕ} {hsp : s ≤ p} {hsq : s ≤ q}
    (C : OverlapConfiguration p q s hsp hsq)
    (A A' : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    overlapFusionKernel C (A + A') B = overlapFusionKernel C A B + overlapFusionKernel C A' B := by
  ext x
  simp only [overlapFusionKernel_apply, subsetPlacement_add, add_apply, map_add]

theorem fusion_add_right {p q s : ℕ} {hsp : s ≤ p} {hsq : s ≤ q}
    (C : OverlapConfiguration p q s hsp hsq)
    (A : BoundedSymmetricKernel H p) (B B' : BoundedSymmetricKernel H q) :
    overlapFusionKernel C A (B + B') = overlapFusionKernel C A B + overlapFusionKernel C A B' := by
  ext x
  simp only [overlapFusionKernel_apply, rightPlacement_add, add_apply, map_add]

#print axioms rightPlacement_add
#print axioms fusion_add_left
#print axioms fusion_add_right
end QuantumNLS.TerraMultiRound20OverlapAdd

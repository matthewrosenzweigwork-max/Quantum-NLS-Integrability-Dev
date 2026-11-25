import QuantumNLS.TerraMultiRound20OverlapAdd
import QuantumNLS.PlacementFiberCanonicalPrefix

/-! Additivity and norm control for the actual averaged overlap kernels. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion QuantumNLS.PlacementProduct
open QuantumNLS.PlacementFiberCanonicalPrefix QuantumNLS.TerraMultiRound20OverlapAdd
namespace QuantumNLS.TerraMultiRound21OverlapContinuity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem average_add_left {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A A' : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    averagedOverlapKernel hsp hsq (A + A') B =
      averagedOverlapKernel hsp hsq A B + averagedOverlapKernel hsp hsq A' B := by
  obtain ⟨C⟩ := overlapConfiguration_nonempty hsp hsq
  simp only [averagedOverlapKernel_eq_overlapFusionKernel hsp hsq C, fusion_add_left]
  rfl

theorem average_add_right {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (B B' : BoundedSymmetricKernel H q) :
    averagedOverlapKernel hsp hsq A (B + B') =
      averagedOverlapKernel hsp hsq A B + averagedOverlapKernel hsp hsq A B' := by
  obtain ⟨C⟩ := overlapConfiguration_nonempty hsp hsq
  simp only [averagedOverlapKernel_eq_overlapFusionKernel hsp hsq C, fusion_add_right]
  rfl

theorem average_zero_left {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (B : BoundedSymmetricKernel H q) :
    averagedOverlapKernel hsp hsq 0 B = 0 := by
  have h := average_add_left hsp hsq (0 : BoundedSymmetricKernel H p) 0 B
  simpa using h

theorem average_zero_right {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) :
    averagedOverlapKernel hsp hsq A 0 = 0 := by
  have h := average_add_right hsp hsq A (0 : BoundedSymmetricKernel H q) 0
  simpa using h

theorem average_sub_left {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A A' : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    averagedOverlapKernel hsp hsq (A - A') B =
      averagedOverlapKernel hsp hsq A B - averagedOverlapKernel hsp hsq A' B := by
  apply eq_sub_iff_add_eq.mpr
  rw [← average_add_left, sub_add_cancel]

theorem average_sub_right {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (B B' : BoundedSymmetricKernel H q) :
    averagedOverlapKernel hsp hsq A (B - B') =
      averagedOverlapKernel hsp hsq A B - averagedOverlapKernel hsp hsq A B' := by
  apply eq_sub_iff_add_eq.mpr
  rw [← average_add_right, sub_add_cancel]

theorem average_difference_bound {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A A' : BoundedSymmetricKernel H p) (B B' : BoundedSymmetricKernel H q) :
    ‖averagedOverlapKernel hsp hsq A B - averagedOverlapKernel hsp hsq A' B'‖ ≤
      ‖A - A'‖ * ‖B‖ + ‖A'‖ * ‖B - B'‖ := by
  calc
    _ = ‖averagedOverlapKernel hsp hsq (A - A') B +
        averagedOverlapKernel hsp hsq A' (B - B')‖ := by
          rw [average_sub_left, average_sub_right]; congr 1; abel
    _ ≤ ‖averagedOverlapKernel hsp hsq (A - A') B‖ +
        ‖averagedOverlapKernel hsp hsq A' (B - B')‖ := by
          exact norm_add_le (averagedOverlapKernel hsp hsq (A - A') B)
            (averagedOverlapKernel hsp hsq A' (B - B'))
    _ ≤ _ := add_le_add (norm_averagedOverlapKernel_le hsp hsq _ _)
      (norm_averagedOverlapKernel_le hsp hsq _ _)

#print axioms average_add_left
#print axioms average_add_right
#print axioms average_zero_left
#print axioms average_zero_right
#print axioms average_sub_left
#print axioms average_sub_right
#print axioms average_difference_bound
end QuantumNLS.TerraMultiRound21OverlapContinuity

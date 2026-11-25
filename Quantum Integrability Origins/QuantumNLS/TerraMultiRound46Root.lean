import QuantumNLS.TerraMultiRound45TreeSum

/-! Root partition of the ordered Riccati trees. This is a partial result
    towards REG-007, not the scalar expansion. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound46Root
open Finset
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TerraMultiRound45Trees
open QuantumNLS.TerraMultiRound45TreeSum QuantumNLS.TerraMultiRound38SignedPicard

/-- The zero level consists exactly of the free resolvent. -/
theorem tree_level_zero {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u : Ell2) :
    treeLevel hL ha hY κ u 0 = signedCLM L Y hY u := by
  simp [treeLevel, treeTerm]

/-- At each positive level, partition the ordered trees uniquely at the root.
The two subtree sizes range over the antidiagonal. -/
theorem tree_level_succ_root {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u : Ell2) (n : ℕ) :
    treeLevel hL ha hY κ u (n + 1) =
      ∑ ij ∈ antidiagonal n,
        ∑ l ∈ BinaryTree.treesOfNumNodesEq ij.1,
          ∑ r ∈ BinaryTree.treesOfNumNodesEq ij.2,
            treeTerm hL ha hY κ u (.node () l r) := by
  unfold treeLevel
  rw [BinaryTree.treesOfNumNodesEq_succ, sum_biUnion]
  · apply sum_congr rfl
    rintro ⟨i, j⟩ hij
    simp only [BinaryTree.pairwiseNode, sum_map, sum_product]
    rfl
  · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left]
    aesop

#print axioms tree_level_zero
#print axioms tree_level_succ_root
end QuantumNLS.TerraMultiRound46Root

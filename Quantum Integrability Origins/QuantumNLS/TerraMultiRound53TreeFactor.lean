import QuantumNLS.TerraMultiRound50TreeIntegral

/-! Extract the complete scalar prefactor from every ordered nested tree.
The remaining integral is still iterated; it is not a flat orthant integral. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound53TreeFactor
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.TerraMultiRound50TreeIntegral

/-- Nested tree with the resolvent and coupling prefactors removed. -/
def bareTree (L a Y : ℝ) (u : Ell2) : BinaryTree Unit → ℝ → ℂ
  | .nil, x => ∫ v : ℝ in Ioi 0,
      (Real.exp (-v) : ℂ) * physRep L a u (x - v / Y)
  | .node _ left right, x => ∫ v : ℝ in Ioi 0,
      (Real.exp (-v) : ℂ) * (starRingEnd ℂ (physRep L a u (x - v / Y)) *
        bareTree L a Y u left (x - v / Y) * bareTree L a Y u right (x - v / Y))

/-- Each internal node contributes `-κ`, and a tree with `n` internal
nodes has exactly `2n+1` resolvent factors. -/
theorem nestedTree_factor (L a Y κ : ℝ) (u : Ell2)
    (tree : BinaryTree Unit) (x : ℝ) :
    nestedTree L a Y κ u tree x =
      (-(κ : ℂ)) ^ tree.numNodes * (Y⁻¹ : ℂ) ^ (2 * tree.numNodes + 1) *
        bareTree L a Y u tree x := by
  induction tree generalizing x with
  | nil => simp [nestedTree, bareTree, BinaryTree.numNodes]
  | node v left right ihl ihr =>
      cases v
      simp only [nestedTree, bareTree, BinaryTree.numNodes, ihl, ihr]
      rw [← integral_const_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      have h : 2 * (left.numNodes + right.numNodes + 1) + 1 =
          (2 * left.numNodes + 1) + (2 * right.numNodes + 1) + 1 := by omega
      rw [h]
      simp only [pow_add, pow_succ]
      ring


/-- The prefactor formula applies to the physical Sobolev tree itself. -/
theorem physicalTree_factor {L a Y : ℝ} [Fact (0 < L)] (hL : 0 < L)
    (ha : 1 / 2 < a) (hY : 0 < |Y|) (κ : ℝ) (u : Ell2)
    (tree : BinaryTree Unit) (x : ℝ) :
    physRep L a (QuantumNLS.TerraMultiRound45Trees.treeTerm hL ha hY κ u tree) x =
      (-(κ : ℂ)) ^ tree.numNodes * (Y⁻¹ : ℂ) ^ (2 * tree.numNodes + 1) *
        bareTree L a Y u tree x := by
  rw [← nestedTree_eq_physical hL ha hY κ u tree x]
  exact nestedTree_factor L a Y κ u tree x

#print axioms physicalTree_factor

#print axioms nestedTree_factor
end QuantumNLS.TerraMultiRound53TreeFactor

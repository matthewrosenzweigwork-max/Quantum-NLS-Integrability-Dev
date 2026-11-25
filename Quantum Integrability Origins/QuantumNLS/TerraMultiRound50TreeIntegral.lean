import QuantumNLS.TerraMultiRound50TreeRecursion

/-! The recursive physical tree is exactly the nested Laplace integral.
Flattening the nested integrals to a single path correlation remains separate. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound50TreeIntegral
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.TerraMultiRound45Trees QuantumNLS.TerraMultiRound50TreeRecursion

/-- The ordered tree evaluated directly by its nested physical shift integrals. -/
def nestedTree (L a Y κ : ℝ) (u : Ell2) : BinaryTree Unit → ℝ → ℂ
  | .nil, x => (Y⁻¹ : ℂ) * ∫ v : ℝ in Ioi 0,
      (Real.exp (-v) : ℂ) * physRep L a u (x - v / Y)
  | .node _ left right, x => -(κ : ℂ) * (Y⁻¹ : ℂ) * ∫ v : ℝ in Ioi 0,
      (Real.exp (-v) : ℂ) * (starRingEnd ℂ (physRep L a u (x - v / Y)) *
        nestedTree L a Y κ u left (x - v / Y) *
        nestedTree L a Y κ u right (x - v / Y))

/-- The exact physical evaluation has all recursive signs, coupling and
resolvent factors; no convergence or tree-size hypothesis is added. -/
theorem nestedTree_eq_physical {L a Y : ℝ} [Fact (0 < L)] (hL : 0 < L)
    (ha : 1 / 2 < a) (hY : 0 < |Y|) (κ : ℝ) (u : Ell2)
    (tree : BinaryTree Unit) (x : ℝ) :
    nestedTree L a Y κ u tree x = physRep L a (treeTerm hL ha hY κ u tree) x := by
  induction tree generalizing x with
  | nil => exact (tree_leaf_laplace hL ha hY κ u x).symm
  | node v left right ihl ihr =>
    cases v
    rw [tree_node_laplace hL ha hY κ u left right x]
    simp only [nestedTree, ihl, ihr]

#print axioms nestedTree_eq_physical
end QuantumNLS.TerraMultiRound50TreeIntegral

import QuantumNLS.TerraMultiRound55ParentTime
import QuantumNLS.TerraMultiRound55KernelFubini

/-! Pointwise root/child decomposition of the physical vertex product. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound56ProductSplit
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound54IndexSplit
open QuantumNLS.TerraMultiRound54PathSplit
open QuantumNLS.TerraMultiRound48TreeFubini
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound55ShiftSplit
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev

variable {L : ℝ} [Fact (0 < L)]

def vertexValue {k : ℕ} (hk : 1 ≤ k) (u : Ell2) (t : BinaryTree Unit)
    (Y : ℝ) (time : Fin (2 * t.numNodes + 1) → ℝ) (x : AddCircle L)
    (i : Fin (2 * t.numNodes + 1)) : ℂ :=
  contRep hk (vertexField (L := L) k u t i)
    (x + ((pathShift (finiteFactorPaths t) Y time ((finSuccEquiv _).symm (some i)) : ℝ) : AddCircle L))

/-- The finite vertex product splits into the root and the two subtrees. -/
theorem vertex_product_node {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (l r : BinaryTree Unit) (Y : ℝ)
    (time : Fin (2 * (BinaryTree.node () l r).numNodes + 1) → ℝ)
    (x : AddCircle L) :
    (∏ i, vertexValue hk u (.node () l r) Y time x i) =
      contRep hk (QuantumNLS.TerraMultiRound49SobolevBridge.physicalToHk (L := L) k
        (QuantumNLS.ComplexifiedSobolevField.jEll u))
        (x + ((-time (rootIndex (.node () l r)) / Y : ℝ) : AddCircle L)) *
      (∏ i, vertexValue hk u l Y (fun j => time (leftIndex l r j))
        (x + ((-time (rootIndex (.node () l r)) / Y : ℝ) : AddCircle L)) i) *
      (∏ i, vertexValue hk u r Y (fun j => time (rightIndex l r j))
        (x + ((-time (rootIndex (.node () l r)) / Y : ℝ) : AddCircle L)) i) := by
  rw [← (splitEquiv l r).prod_comp]
  rw [Fintype.prod_option, Fintype.prod_sum_type]
  dsimp only [splitEquiv, Equiv.ofBijective, Equiv.coe_fn_mk, splitIndex]
  simp only [vertexValue, vertexField_root_node, root_factor_shift,
    vertexField_left, vertexField_right, left_factor_shift, right_factor_shift,
    AddCircle.coe_add, add_assoc, mul_assoc]

/-- The exponential density obeys the same finite reindexing. -/
theorem exponential_product_node (l r : BinaryTree Unit)
    (time : Fin (2 * (BinaryTree.node () l r).numNodes + 1) → ℝ) :
    (∏ i, Real.exp (-time i)) =
      Real.exp (-time (rootIndex (.node () l r))) *
      (∏ i, Real.exp (-time (leftIndex l r i))) *
      (∏ i, Real.exp (-time (rightIndex l r i))) := by
  rw [← (splitEquiv l r).prod_comp]
  rw [Fintype.prod_option, Fintype.prod_sum_type]
  dsimp only [splitEquiv, Equiv.ofBijective, Equiv.coe_fn_mk, splitIndex]
  simp only [mul_assoc]

#print axioms vertex_product_node
#print axioms exponential_product_node
end QuantumNLS.TerraMultiRound56ProductSplit

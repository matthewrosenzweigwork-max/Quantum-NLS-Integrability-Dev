import QuantumNLS.TerraMultiRound56ProductSplit

/-! The concrete orthant kernel factors at the tree root. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound56KernelSplit
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound54PathSplit
open QuantumNLS.TerraMultiRound48TreeFubini
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound55ShiftSplit
open QuantumNLS.TerraMultiRound56ProductSplit
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev

variable {L : ℝ} [Fact (0 < L)]

def vertexKernel {k : ℕ} (hk : 1 ≤ k) (u : Ell2) (t : BinaryTree Unit)
    (Y : ℝ) (time : Fin (2 * t.numNodes + 1) → ℝ) (x : AddCircle L) : ℂ :=
  ((∏ i, Real.exp (-time i) : ℝ) : ℂ) * ∏ i, vertexValue hk u t Y time x i

/-- The spatial pairing factor is separated from the vertex kernel. -/
theorem treeIntegrand_eq_outer_mul {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (t : BinaryTree Unit) (Y : ℝ) (time : Fin (2 * t.numNodes + 1) → ℝ)
    (x : AddCircle L) :
    treeIntegrand hk (factorField (L := L) k u t) (finiteFactorPaths t) Y (time, x) =
      contRep hk (QuantumNLS.TerraMultiRound49SobolevBridge.physicalToHk (L := L) k
        (QuantumNLS.ComplexifiedSobolevField.jEll u)) x * vertexKernel hk u t Y time x := by
  unfold treeIntegrand vertexKernel
  rw [← ((finSuccEquiv (2 * t.numNodes + 1)).symm).prod_comp]
  rw [Fintype.prod_option]
  simp only [factorField_outer, factorField_vertex, outer_factor_shift,
    AddCircle.coe_zero, add_zero, vertexValue]
  ring

/-- The actual kernel separates pointwise into the root and child kernels. -/
theorem vertexKernel_node {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (l r : BinaryTree Unit) (Y : ℝ)
    (time : Fin (2 * (BinaryTree.node () l r).numNodes + 1) → ℝ)
    (x : AddCircle L) :
    vertexKernel hk u (.node () l r) Y time x =
      (Real.exp (-time (rootIndex (.node () l r))) : ℂ) *
      contRep hk (QuantumNLS.TerraMultiRound49SobolevBridge.physicalToHk (L := L) k
        (QuantumNLS.ComplexifiedSobolevField.jEll u))
        (x + ((-time (rootIndex (.node () l r)) / Y : ℝ) : AddCircle L)) *
      vertexKernel hk u l Y (fun j => time (leftIndex l r j))
        (x + ((-time (rootIndex (.node () l r)) / Y : ℝ) : AddCircle L)) *
      vertexKernel hk u r Y (fun j => time (rightIndex l r j))
        (x + ((-time (rootIndex (.node () l r)) / Y : ℝ) : AddCircle L)) := by
  unfold vertexKernel
  rw [exponential_product_node, vertex_product_node]
  push_cast
  ring

#print axioms treeIntegrand_eq_outer_mul
#print axioms vertexKernel_node
end QuantumNLS.TerraMultiRound56KernelSplit

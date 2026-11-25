import QuantumNLS.TerraMultiRound56VertexFubini

/-! Recursive integration of the unpaired flat tree kernel. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound56FlatRecursion
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound54PathSplit
open QuantumNLS.TerraMultiRound54RootFubini
open QuantumNLS.TerraMultiRound55ChildFubini
open QuantumNLS.TerraMultiRound55PhysicalChildren
open QuantumNLS.TerraMultiRound55ParentTime
open QuantumNLS.TerraMultiRound56KernelSplit
open QuantumNLS.TerraMultiRound56VertexFubini
open QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

def flatTree {k : ℕ} (hk : 1 ≤ k) (u : Ell2) (t : BinaryTree Unit)
    (Y : ℝ) (x : AddCircle L) : ℂ :=
  ∫ time, vertexKernel hk u t Y time x ∂
    (Measure.pi (fun _ : Fin (2 * t.numNodes + 1) => positiveMeasure))

/-- The flat parent integral has exactly the nested root/child recursion. -/
theorem flatTree_node {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (l r : BinaryTree Unit) (Y : ℝ) (x : AddCircle L) :
    flatTree hk u (.node () l r) Y x =
      ∫ v : ℝ, (Real.exp (-v) : ℂ) *
        contRep hk (QuantumNLS.TerraMultiRound49SobolevBridge.physicalToHk (L := L) k
          (QuantumNLS.ComplexifiedSobolevField.jEll u)) (x + ((-v / Y : ℝ) : AddCircle L)) *
        flatTree hk u l Y (x + ((-v / Y : ℝ) : AddCircle L)) *
        flatTree hk u r Y (x + ((-v / Y : ℝ) : AddCircle L)) ∂positiveMeasure := by
  change (∫ time, vertexKernel hk u (.node () l r) Y time x ∂
    (Measure.pi (fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => positiveMeasure))) = _
  rw [vertex_root_fubini]
  apply integral_congr_ae
  filter_upwards [vertex_children_fubini hk u l r Y x] with v hv
  rw [hv]
  simp only [vertexKernel_node, parentTime_root, parentTime_left, parentTime_right]
  simp only [childAssembly, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
    Equiv.sumPiEquivProdPi_symm_apply, Sum.elim_inl, Sum.elim_inr]
  simp only [integral_mul_const, integral_const_mul, flatTree]

#print axioms flatTree_node
end QuantumNLS.TerraMultiRound56FlatRecursion

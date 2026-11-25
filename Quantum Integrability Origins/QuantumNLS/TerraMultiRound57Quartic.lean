import QuantumNLS.TerraMultiRound57FirstCoefficient
import QuantumNLS.TerraMultiRound56ProductSplit
import QuantumNLS.TerraMultiRound52Quartic

/-! Identify the one-node zero-shift physical tree with the quartic integral. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound57Quartic
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound48TreeFubini
open QuantumNLS.TerraMultiRound53TreeIndex QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound56ProductSplit QuantumNLS.TerraMultiRound52Quartic
open QuantumNLS.TerraMultiRound51TaylorIntegral QuantumNLS.TerraMultiRound51TaylorLeading
open QuantumNLS.TerraMultiRound57LevelPowers QuantumNLS.TerraMultiRound57FirstCoefficient
variable {L : ℝ} [Fact (0 < L)]

/-- At zero shift, the unique one-node tree gives the quartic scalar integral. -/
theorem one_tree_quartic {k : ℕ} (hk : 1 ≤ k) (u : Ell2) :
    integratedCoeff (Cfun (factorField (L := L) k u (.node () .nil .nil)))
      (finiteFactorPaths (.node () .nil .nil)) 0 =
      ∫ x : AddCircle L, ((‖contRep hk (physicalToHk (L := L) k u) x‖ ^ 4 : ℝ) : ℂ)
        ∂(volume : Measure (AddCircle L)) := by
  rw [integratedCoeff_zero, Cfun_eq_cont hk]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Pi.zero_apply, AddCircle.coe_zero, add_zero]
  let t : BinaryTree Unit := .node () .nil .nil
  have hz (v : BinaryTree Unit) (i : Fin (2 * v.numNodes + 1)) :
      vertexValue hk u v 1 (fun _ => 0) x i = contRep hk (vertexField (L := L) k u v i) x := by
    simp [vertexValue, pathShift]
  have hl : (∏ i : Fin (2 * (BinaryTree.nil : BinaryTree Unit).numNodes + 1),
      vertexValue hk u .nil 1 (fun _ => 0) x i) = contRep hk (physicalToHk (L := L) k u) x := by
    letI : Subsingleton (Fin (2 * (BinaryTree.nil : BinaryTree Unit).numNodes + 1)) := by
      change Subsingleton (Fin 1)
      infer_instance
    rw [Fintype.prod_subsingleton _ (rootIndex .nil)]
    rw [hz, vertexField_root_leaf]
  have hv := vertex_product_node hk u .nil .nil 1 (fun _ => 0) x
  simp only [Pi.zero_apply, neg_zero, zero_div, AddCircle.coe_zero, add_zero] at hv
  rw [hl] at hv
  simp_rw [hz] at hv
  rw [← ((finSuccEquiv (2 * t.numNodes + 1)).symm).prod_comp]
  rw [Fintype.prod_option]
  simp only [factorField, Equiv.apply_symm_apply]
  change contRep hk (physicalToHk (L := L) k (jEll u)) x *
    (∏ i, contRep hk (vertexField (L := L) k u t i) x) = _
  rw [show (∏ i, contRep hk (vertexField (L := L) k u t i) x) =
    contRep hk (physicalToHk (L := L) k (jEll u)) x *
      contRep hk (physicalToHk (L := L) k u) x *
      contRep hk (physicalToHk (L := L) k u) x from hv]
  rw [conjugate_rep hk u x]
  let z := contRep hk (physicalToHk (L := L) k u) x
  have hz' : starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  change starRingEnd ℂ z * (starRingEnd ℂ z * z * z) = _
  calc
    _ = (starRingEnd ℂ z * z) * (starRingEnd ℂ z * z) := by ring
    _ = ((‖z‖ ^ 4 : ℝ) : ℂ) := by rw [hz']; push_cast; ring

/-- The inverse-cube tree coefficient is the negative quartic interaction. -/
theorem tree_coefficient_three_quartic {k : ℕ} (hk : 1 ≤ k) (κ : ℝ)
    (u : Ell2) (s : ℕ) (hs : 1 ≤ s) :
    QuantumNLS.TerraMultiRound57CollectedPowers.treeCoefficient (L := L) (k := k) κ u s 3 =
      -(κ : ℂ) * ∫ x : AddCircle L, ((‖contRep hk (physicalToHk (L := L) k u) x‖ ^ 4 : ℝ) : ℂ)
        ∂(volume : Measure (AddCircle L)) := by
  rw [tree_coefficient_three κ u s hs]
  unfold levelCoeff
  have htree : BinaryTree.treesOfNumNodesEq 1 = {BinaryTree.node () .nil .nil} := by
    rw [BinaryTree.treesOfNumNodesEq_succ]
    simp [BinaryTree.pairwiseNode]
    rfl
  rw [htree, Finset.sum_singleton, one_tree_quartic hk]
  simp [BinaryTree.numNodes]

#print axioms one_tree_quartic
#print axioms tree_coefficient_three_quartic
end QuantumNLS.TerraMultiRound57Quartic

import QuantumNLS.TerraMultiRound56FlatRecursion
import QuantumNLS.TerraMultiRound53TreeFactor

/-! Identification of the flat vertex integral with the nested bare tree. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound56TreeBridge
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound53TreeFactor
open QuantumNLS.TerraMultiRound54RootFubini
open QuantumNLS.TerraMultiRound48TreeFubini
open QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound55ShiftSplit
open QuantumNLS.TerraMultiRound56ProductSplit
open QuantumNLS.TerraMultiRound56KernelSplit
open QuantumNLS.TerraMultiRound56FlatRecursion
open QuantumNLS.TerraMultiRound49SobolevBridge
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

/-- A leaf has one time variable and one un-conjugated field factor. -/
theorem flatTree_leaf {k : ℕ} (hk : 1 ≤ k) (u : Ell2) (Y : ℝ) (x : AddCircle L) :
    flatTree hk u .nil Y x = ∫ v : ℝ, (Real.exp (-v) : ℂ) *
      contRep hk (physicalToHk (L := L) k u) (x + ((-v / Y : ℝ) : AddCircle L)) ∂positiveMeasure := by
  unfold flatTree
  haveI : Unique (Fin (2 * (BinaryTree.nil : BinaryTree Unit).numNodes + 1)) := by
    change Unique (Fin 1)
    infer_instance
  letI : Fintype (Fin (2 * (BinaryTree.nil : BinaryTree Unit).numNodes + 1)) := Fin.fintype _
  have hp := (measurePreserving_funUnique positiveMeasure
    (Fin (2 * (BinaryTree.nil : BinaryTree Unit).numNodes + 1))).symm
  have h := hp.integral_comp' (fun time => vertexKernel hk u .nil Y time x)
  have hfi : (Unique.fintype : Fintype (Fin (2 * (BinaryTree.nil : BinaryTree Unit).numNodes + 1))) = Fin.fintype _ := Subsingleton.elim _ _
  rw [hfi] at h
  refine h.symm.trans ?_
  apply integral_congr_ae
  filter_upwards with v
  simp only [vertexKernel, Fintype.prod_unique, vertexValue]
  have hf (i : Fin (2 * (BinaryTree.nil : BinaryTree Unit).numNodes + 1)) :
      vertexField (L := L) k u .nil i = physicalToHk (L := L) k u := by
    have hi : i = rootIndex .nil := Subsingleton.elim _ _
    rw [hi, vertexField_root_leaf]
  have hs (time : Fin (2 * (BinaryTree.nil : BinaryTree Unit).numNodes + 1) → ℝ)
      (i : Fin (2 * (BinaryTree.nil : BinaryTree Unit).numNodes + 1)) :
      pathShift (finiteFactorPaths .nil) Y time ((finSuccEquiv _).symm (some i)) = -time i / Y := by
    have hi : i = rootIndex .nil := Subsingleton.elim _ _
    subst i
    exact root_factor_shift .nil Y time
  simp only [hf, hs]
  rfl

/-- The unpaired flat orthant integral is the recursively nested bare tree. -/
theorem flatTree_eq_bareTree {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (t : BinaryTree Unit) (Y x : ℝ) :
    flatTree hk u t Y (x : AddCircle L) = bareTree L (k : ℝ) Y u t x := by
  induction t generalizing x with
  | nil =>
    rw [flatTree_leaf]
    simp only [bareTree]
    apply integral_congr_ae
    filter_upwards with v
    have hx : (x : AddCircle L) + ((-v / Y : ℝ) : AddCircle L) =
        ((x - v / Y : ℝ) : AddCircle L) := by simp [sub_eq_add_neg, neg_div]
    rw [hx, physicalToHk_rep]
  | node a l r ihl ihr =>
    cases a
    rw [flatTree_node]
    simp only [bareTree]
    apply integral_congr_ae
    filter_upwards with v
    have hx : (x : AddCircle L) + ((-v / Y : ℝ) : AddCircle L) =
        ((x - v / Y : ℝ) : AddCircle L) := by simp [sub_eq_add_neg, neg_div, AddCircle.coe_add]
    rw [hx, ihl, ihr, physicalToHk_conj_rep]
    ring

#print axioms flatTree_leaf
#print axioms flatTree_eq_bareTree
end QuantumNLS.TerraMultiRound56TreeBridge

import QuantumNLS.TerraMultiRound54RootFubini
import QuantumNLS.TerraMultiRound48TreeFubini
import QuantumNLS.TerraMultiRound49SobolevBridge

/-! The physical field assignment for the finite path correlation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound54PathSplit
open QuantumNLS.TerraMultiRound48TreeFubini
open QuantumNLS.TerraMultiRound49SobolevBridge
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

/-- A vertex carries the conjugated field exactly when its subtree has
an internal node at that address. Invalid addresses are irrelevant. -/
def internalAt : BinaryTree Unit → List Bool → Bool
  | .nil, _ => false
  | .node _ _ _, [] => true
  | .node _ l _, false :: v => internalAt l v
  | .node _ _ r, true :: v => internalAt r v

def vertexField (k : ℕ) (u : Ell2) (t : BinaryTree Unit)
    (i : Fin (2 * t.numNodes + 1)) : Hk L k :=
  if internalAt t (indexedVertex t i) then physicalToHk (L := L) k (jEll u)
  else physicalToHk (L := L) k u

/-- The outer scalar factor is conjugated; vertices use their own type. -/
def factorField (k : ℕ) (u : Ell2) (t : BinaryTree Unit) :
    Fin ((2 * t.numNodes + 1) + 1) → Hk L k := fun i =>
  match finSuccEquiv (2 * t.numNodes + 1) i with
  | none => physicalToHk (L := L) k (jEll u)
  | some j => vertexField (L := L) k u t j

@[simp] theorem vertexField_root_node (k : ℕ) (u : Ell2) (l r : BinaryTree Unit) :
    vertexField (L := L) k u (.node () l r) (rootIndex (.node () l r)) =
      physicalToHk (L := L) k (jEll u) := by
  simp [vertexField, internalAt]

@[simp] theorem vertexField_root_leaf (k : ℕ) (u : Ell2) :
    vertexField (L := L) k u .nil (rootIndex .nil) = physicalToHk (L := L) k u := by
  simp [vertexField, internalAt]

@[simp] theorem vertexField_left (k : ℕ) (u : Ell2) (l r : BinaryTree Unit)
    (i : Fin (2 * l.numNodes + 1)) :
    vertexField (L := L) k u (.node () l r) (leftIndex l r i) = vertexField (L := L) k u l i := by
  simp [vertexField, internalAt]

@[simp] theorem vertexField_right (k : ℕ) (u : Ell2) (l r : BinaryTree Unit)
    (i : Fin (2 * r.numNodes + 1)) :
    vertexField (L := L) k u (.node () l r) (rightIndex l r i) = vertexField (L := L) k u r i := by
  simp [vertexField, internalAt]

@[simp] theorem factorField_outer (k : ℕ) (u : Ell2) (t : BinaryTree Unit) :
    factorField (L := L) k u t ((finSuccEquiv (2 * t.numNodes + 1)).symm none) =
      physicalToHk (L := L) k (jEll u) := by simp [factorField]

@[simp] theorem factorField_vertex (k : ℕ) (u : Ell2) (t : BinaryTree Unit)
    (i : Fin (2 * t.numNodes + 1)) :
    factorField (L := L) k u t ((finSuccEquiv (2 * t.numNodes + 1)).symm (some i)) =
      vertexField (L := L) k u t i := by simp [factorField]

/-- The actual joint physical-factor kernel is integrable, including the
spatial pairing and without an assumed Fubini premise. -/
theorem physical_kernel_integrable {k : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (t : BinaryTree Unit) (Y : ℝ) :
    Integrable (treeIntegrand hk (factorField (L := L) k u t) (finiteFactorPaths t) Y)
      ((Measure.pi (fun _ : Fin (2 * t.numNodes + 1) =>
        volume.restrict (Ioi (0 : ℝ)))).prod (volume : Measure (AddCircle L))) :=
  tree_integrable hk (factorField (L := L) k u t) (finiteFactorPaths t) Y

#print axioms vertexField_root_node
#print axioms vertexField_root_leaf
#print axioms vertexField_left
#print axioms vertexField_right
#print axioms factorField_outer
#print axioms factorField_vertex
#print axioms physical_kernel_integrable
end QuantumNLS.TerraMultiRound55TreeFactors

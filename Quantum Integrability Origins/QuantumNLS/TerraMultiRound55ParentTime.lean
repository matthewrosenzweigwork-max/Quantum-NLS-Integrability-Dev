import QuantumNLS.TerraMultiRound55PhysicalChildren
import QuantumNLS.TerraMultiRound55ShiftSplit

/-! Coordinate values of the recursively assembled parent time vector. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound55ParentTime
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound54IndexSplit
open QuantumNLS.TerraMultiRound54PathSplit
open QuantumNLS.TerraMultiRound54RootFubini
open QuantumNLS.TerraMultiRound55PhysicalChildren

@[simp] theorem parentTime_root (l r : BinaryTree Unit)
    (sub : (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) → ℝ) (root : ℝ) :
    parentTime l r sub root (rootIndex (.node () l r)) = root := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => ℝ)
    (splitEquiv l r) (optionAssembly (sub, root)) none
  change parentTime l r sub root (rootIndex (.node () l r)) = root at h
  exact h

@[simp] theorem parentTime_left (l r : BinaryTree Unit)
    (sub : (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) → ℝ) (root : ℝ)
    (i : Fin (2 * l.numNodes + 1)) :
    parentTime l r sub root (leftIndex l r i) = sub (.inl i) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => ℝ)
    (splitEquiv l r) (optionAssembly (sub, root)) (some (.inl i))
  change parentTime l r sub root (leftIndex l r i) = sub (.inl i) at h
  exact h

@[simp] theorem parentTime_right (l r : BinaryTree Unit)
    (sub : (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) → ℝ) (root : ℝ)
    (i : Fin (2 * r.numNodes + 1)) :
    parentTime l r sub root (rightIndex l r i) = sub (.inr i) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : Fin (2 * (BinaryTree.node () l r).numNodes + 1) => ℝ)
    (splitEquiv l r) (optionAssembly (sub, root)) (some (.inr i))
  change parentTime l r sub root (rightIndex l r i) = sub (.inr i) at h
  exact h

#print axioms parentTime_root
#print axioms parentTime_left
#print axioms parentTime_right
end QuantumNLS.TerraMultiRound55ParentTime

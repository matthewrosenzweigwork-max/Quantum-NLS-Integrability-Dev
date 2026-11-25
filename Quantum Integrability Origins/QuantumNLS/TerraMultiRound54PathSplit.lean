import QuantumNLS.TerraMultiRound53TreeIndex
import QuantumNLS.TerraMultiRound48Leading

/-! Recursive path decomposition for the finite tree indexing. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound54PathSplit
open QuantumNLS.TerraMultiRound53TreePaths
open QuantumNLS.TerraMultiRound53TreeIndex

private def consEmb (b : Bool) : List Bool ↪ List Bool where
  toFun := List.cons b
  inj' := by intro x y h; exact (List.cons.inj h).2

@[simp] private theorem consEmb_apply (b : Bool) (v : List Bool) :
    consEmb b v = b :: v := rfl

@[simp] theorem mem_vertices_left (l r : BinaryTree Unit) (v : List Bool) :
    false :: v ∈ vertices (.node () l r) ↔ v ∈ vertices l := by
  change false :: v ∈ insert [] ((vertices l).map (consEmb false) ∪
    (vertices r).map (consEmb true)) ↔ v ∈ vertices l
  simp

@[simp] theorem mem_vertices_right (l r : BinaryTree Unit) (v : List Bool) :
    true :: v ∈ vertices (.node () l r) ↔ v ∈ vertices r := by
  change true :: v ∈ insert [] ((vertices l).map (consEmb false) ∪
    (vertices r).map (consEmb true)) ↔ v ∈ vertices r
  simp

/-- The path to a left descendant consists precisely of the root and the
left-prefixed path inside the left subtree. -/
theorem path_left (l r : BinaryTree Unit) (v : List Bool) :
    path (.node () l r) (false :: v) = insert [] ((path l v).map (consEmb false)) := by
  ext w
  cases w with
  | nil => simp [path, consEmb]
  | cons b w =>
    cases b <;> simp [path, List.cons_prefix_cons]

/-- The analogous decomposition for a right descendant. -/
theorem path_right (l r : BinaryTree Unit) (v : List Bool) :
    path (.node () l r) (true :: v) = insert [] ((path r v).map (consEmb true)) := by
  ext w
  cases w with
  | nil => simp [path, consEmb]
  | cons b w =>
    cases b <;> simp [path, List.cons_prefix_cons]

/-- Exact path-weight decomposition used when splitting the root time from
subtree times. -/
theorem path_sum_left (l r : BinaryTree Unit) (v : List Bool) (w : List Bool → ℝ) :
    ∑ a ∈ path (.node () l r) (false :: v), w a =
      w [] + ∑ a ∈ path l v, w (false :: a) := by
  rw [path_left, Finset.sum_insert]
  · simp
  · simp

theorem path_sum_right (l r : BinaryTree Unit) (v : List Bool) (w : List Bool → ℝ) :
    ∑ a ∈ path (.node () l r) (true :: v), w a =
      w [] + ∑ a ∈ path r v, w (true :: a) := by
  rw [path_right, Finset.sum_insert]
  · simp
  · simp

/-- Address of an indexed time variable is a vertex of the same tree. -/
theorem indexedVertex_mem (t : BinaryTree Unit) (i : Fin (2 * t.numNodes + 1)) :
    indexedVertex t i ∈ vertices t := ((vertexIndex t).symm i).property

theorem indexedVertex_injective (t : BinaryTree Unit) : Function.Injective (indexedVertex t) := by
  intro i j h
  apply (vertexIndex t).symm.injective
  exact Subtype.ext h

/-- Extend a time assignment from the enumerated vertices to all addresses. -/
def addressTime (t : BinaryTree Unit) (time : Fin (2 * t.numNodes + 1) → ℝ)
    (v : List Bool) : ℝ :=
  if hv : v ∈ vertices t then time (vertexIndex t ⟨v, hv⟩) else 0

@[simp] theorem addressTime_indexed (t : BinaryTree Unit)
    (time : Fin (2 * t.numNodes + 1) → ℝ) (i : Fin (2 * t.numNodes + 1)) :
    addressTime t time (indexedVertex t i) = time i := by
  simp [addressTime, indexedVertex, vertexIndex]

/-- The path sum computed from the round 53 finite enumeration is exactly
its address-based path sum. -/
theorem indexed_path_sum (t : BinaryTree Unit)
    (time : Fin (2 * t.numNodes + 1) → ℝ) (i : Fin (2 * t.numNodes + 1)) :
    ∑ j ∈ indexedPath t i, time j =
      ∑ v ∈ path t (indexedVertex t i), addressTime t time v := by
  apply Finset.sum_bij (fun j _ => indexedVertex t j)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨indexedVertex_mem t j, (mem_indexedPath t i j).mp hj⟩
  · intro j hj k hk h
    exact indexedVertex_injective t h
  · intro v hv
    have hv' := Finset.mem_filter.mp hv
    let j := vertexIndex t ⟨v, hv'.1⟩
    have hj : indexedVertex t j = v := by simp [j, indexedVertex]
    refine ⟨j, (mem_indexedPath t i j).mpr ?_, hj⟩
    simpa [hj] using hv'.2
  · intro j hj
    simp

/-- Embed each child's enumerated vertices into the corresponding branch. -/
def leftIndex (l r : BinaryTree Unit) (i : Fin (2 * l.numNodes + 1)) :
    Fin (2 * (BinaryTree.node () l r).numNodes + 1) :=
  vertexIndex (.node () l r) ⟨false :: indexedVertex l i,
    (mem_vertices_left l r _).mpr (indexedVertex_mem l i)⟩

def rightIndex (l r : BinaryTree Unit) (i : Fin (2 * r.numNodes + 1)) :
    Fin (2 * (BinaryTree.node () l r).numNodes + 1) :=
  vertexIndex (.node () l r) ⟨true :: indexedVertex r i,
    (mem_vertices_right l r _).mpr (indexedVertex_mem r i)⟩

@[simp] theorem indexedVertex_left (l r : BinaryTree Unit) (i : Fin (2 * l.numNodes + 1)) :
    indexedVertex (.node () l r) (leftIndex l r i) = false :: indexedVertex l i := by
  change ((vertexIndex (.node () l r)).symm ((vertexIndex (.node () l r))
    ⟨false :: indexedVertex l i, _⟩)).val = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem indexedVertex_right (l r : BinaryTree Unit) (i : Fin (2 * r.numNodes + 1)) :
    indexedVertex (.node () l r) (rightIndex l r i) = true :: indexedVertex r i := by
  change ((vertexIndex (.node () l r)).symm ((vertexIndex (.node () l r))
    ⟨true :: indexedVertex r i, _⟩)).val = _
  rw [Equiv.symm_apply_apply]

/-- At every indexed left vertex, the parent path sum is its root time
plus the corresponding left-subtree path sum. -/
theorem indexed_path_sum_left (l r : BinaryTree Unit)
    (time : Fin (2 * (BinaryTree.node () l r).numNodes + 1) → ℝ)
    (i : Fin (2 * l.numNodes + 1)) :
    ∑ j ∈ indexedPath (.node () l r) (leftIndex l r i), time j =
      time (rootIndex (.node () l r)) + ∑ j ∈ indexedPath l i, time (leftIndex l r j) := by
  rw [indexed_path_sum, indexedVertex_left, path_sum_left, indexed_path_sum]
  have hroot : addressTime (.node () l r) time [] = time (rootIndex (.node () l r)) := by
    simpa using addressTime_indexed (.node () l r) time (rootIndex (.node () l r))
  rw [hroot]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  have hmem := (Finset.mem_filter.mp hv).1
  let j := vertexIndex l ⟨v, hmem⟩
  have hj : indexedVertex l j = v := by simp [j, indexedVertex]
  rw [← hj, ← indexedVertex_left, addressTime_indexed, addressTime_indexed]

/-- The same root-time decomposition for the right subtree. -/
theorem indexed_path_sum_right (l r : BinaryTree Unit)
    (time : Fin (2 * (BinaryTree.node () l r).numNodes + 1) → ℝ)
    (i : Fin (2 * r.numNodes + 1)) :
    ∑ j ∈ indexedPath (.node () l r) (rightIndex l r i), time j =
      time (rootIndex (.node () l r)) + ∑ j ∈ indexedPath r i, time (rightIndex l r j) := by
  rw [indexed_path_sum, indexedVertex_right, path_sum_right, indexed_path_sum]
  have hroot : addressTime (.node () l r) time [] = time (rootIndex (.node () l r)) := by
    simpa using addressTime_indexed (.node () l r) time (rootIndex (.node () l r))
  rw [hroot]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  have hmem := (Finset.mem_filter.mp hv).1
  let j := vertexIndex r ⟨v, hmem⟩
  have hj : indexedVertex r j = v := by simp [j, indexedVertex]
  rw [← hj, ← indexedVertex_right, addressTime_indexed, addressTime_indexed]

#print axioms indexedVertex_left
#print axioms indexedVertex_right
#print axioms indexed_path_sum_left
#print axioms indexed_path_sum_right

#print axioms indexedVertex_mem
#print axioms indexedVertex_injective
#print axioms addressTime_indexed
#print axioms indexed_path_sum

#print axioms mem_vertices_left
#print axioms mem_vertices_right
#print axioms path_left
#print axioms path_right
#print axioms path_sum_left
#print axioms path_sum_right
end QuantumNLS.TerraMultiRound54PathSplit

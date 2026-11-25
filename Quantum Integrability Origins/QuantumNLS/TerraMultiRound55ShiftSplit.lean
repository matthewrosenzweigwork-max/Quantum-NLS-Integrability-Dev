import QuantumNLS.TerraMultiRound55TreeFactors

/-! Shift decomposition for the physical parent and child factor paths. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound55ShiftSplit
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound54PathSplit
open QuantumNLS.TerraMultiRound48TreeFubini

/-- The shift of a left child vertex is the root shift followed by its
shift within the left subtree. -/
theorem left_factor_shift (l r : BinaryTree Unit) (Y : ℝ)
    (time : Fin (2 * (BinaryTree.node () l r).numNodes + 1) → ℝ)
    (i : Fin (2 * l.numNodes + 1)) :
    pathShift (finiteFactorPaths (.node () l r)) Y time
      ((finSuccEquiv _).symm (some (leftIndex l r i))) =
    -time (rootIndex (.node () l r)) / Y +
      pathShift (finiteFactorPaths l) Y (fun j => time (leftIndex l r j))
        ((finSuccEquiv _).symm (some i)) := by
  simp only [pathShift, finiteFactorPaths_vertex, indexed_path_sum_left]
  ring

/-- The same identity holds for a right child vertex. -/
theorem right_factor_shift (l r : BinaryTree Unit) (Y : ℝ)
    (time : Fin (2 * (BinaryTree.node () l r).numNodes + 1) → ℝ)
    (i : Fin (2 * r.numNodes + 1)) :
    pathShift (finiteFactorPaths (.node () l r)) Y time
      ((finSuccEquiv _).symm (some (rightIndex l r i))) =
    -time (rootIndex (.node () l r)) / Y +
      pathShift (finiteFactorPaths r) Y (fun j => time (rightIndex l r j))
        ((finSuccEquiv _).symm (some i)) := by
  simp only [pathShift, finiteFactorPaths_vertex, indexed_path_sum_right]
  ring


/-- The root path consists of the root alone. -/
theorem indexedPath_root (t : BinaryTree Unit) :
    indexedPath t (rootIndex t) = {rootIndex t} := by
  ext j
  simp only [mem_indexedPath, root_vertex, List.prefix_nil, Finset.mem_singleton]
  constructor
  · intro h
    apply indexedVertex_injective t
    simpa using h
  · intro h
    subst j
    simp

/-- The root and outer factors use the expected shifts. -/
theorem root_factor_shift (t : BinaryTree Unit) (Y : ℝ)
    (time : Fin (2 * t.numNodes + 1) → ℝ) :
    pathShift (finiteFactorPaths t) Y time
      ((finSuccEquiv _).symm (some (rootIndex t))) = -time (rootIndex t) / Y := by
  simp only [pathShift, finiteFactorPaths_vertex, indexedPath_root, Finset.sum_singleton]

theorem outer_factor_shift (t : BinaryTree Unit) (Y : ℝ)
    (time : Fin (2 * t.numNodes + 1) → ℝ) :
    pathShift (finiteFactorPaths t) Y time ((finSuccEquiv _).symm none) = 0 := by
  simp only [pathShift, finiteFactorPaths_outer, Finset.sum_empty, neg_zero, zero_div]

#print axioms left_factor_shift
#print axioms right_factor_shift
#print axioms indexedPath_root
#print axioms root_factor_shift
#print axioms outer_factor_shift
end QuantumNLS.TerraMultiRound55ShiftSplit

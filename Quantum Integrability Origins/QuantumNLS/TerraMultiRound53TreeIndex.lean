import QuantumNLS.TerraMultiRound53TreePaths

/-! Finite indexing of the canonical tree addresses for the path-correlation
interface. This does not assert the analytic tree-to-orthant identity. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound53TreePaths

/-- An enumeration of the canonical vertex addresses by the number of
resolvent variables. The choice of enumeration has no geometric meaning. -/
def vertexIndex (t : BinaryTree Unit) :
    {v // v ∈ vertices t} ≃ Fin (2 * t.numNodes + 1) :=
  Finset.equivFinOfCardEq (card_vertices t)

def indexedVertex (t : BinaryTree Unit) (i : Fin (2 * t.numNodes + 1)) : List Bool :=
  ((vertexIndex t).symm i).val

/-- Time variables on the root-to-vertex path, in the indexing expected by
`pathShift` and `integratedCorrelation`. -/
def indexedPath (t : BinaryTree Unit) (i : Fin (2 * t.numNodes + 1)) :
    Finset (Fin (2 * t.numNodes + 1)) :=
  Finset.univ.filter (fun j => indexedVertex t j <+: indexedVertex t i)

@[simp] theorem mem_indexedPath (t : BinaryTree Unit)
    (i j : Fin (2 * t.numNodes + 1)) :
    j ∈ indexedPath t i ↔ indexedVertex t j <+: indexedVertex t i := by
  simp [indexedPath]

@[simp] theorem self_mem_indexedPath (t : BinaryTree Unit)
    (i : Fin (2 * t.numNodes + 1)) : i ∈ indexedPath t i := by
  simp

def rootIndex (t : BinaryTree Unit) : Fin (2 * t.numNodes + 1) :=
  vertexIndex t ⟨[], root_mem t⟩

@[simp] theorem root_vertex (t : BinaryTree Unit) : indexedVertex t (rootIndex t) = [] := by
  simp [indexedVertex, rootIndex]

@[simp] theorem root_mem_indexedPath (t : BinaryTree Unit)
    (i : Fin (2 * t.numNodes + 1)) : rootIndex t ∈ indexedPath t i := by
  simp

/-- The outer scalar-pairing factor has empty path; each of the other
factors corresponds bijectively to one tree vertex. -/
def factorPaths (t : BinaryTree Unit) :
    Option (Fin (2 * t.numNodes + 1)) → Finset (Fin (2 * t.numNodes + 1))
  | none => ∅
  | some i => indexedPath t i


/-- The same path family on `Fin`, with `2n+2` scalar factors. -/
def finiteFactorPaths (t : BinaryTree Unit) :
    Fin ((2 * t.numNodes + 1) + 1) → Finset (Fin (2 * t.numNodes + 1)) :=
  fun i => factorPaths t (finSuccEquiv (2 * t.numNodes + 1) i)

@[simp] theorem finiteFactorPaths_outer (t : BinaryTree Unit) :
    finiteFactorPaths t ((finSuccEquiv (2 * t.numNodes + 1)).symm none) = ∅ := by
  simp [finiteFactorPaths, factorPaths]

@[simp] theorem finiteFactorPaths_vertex (t : BinaryTree Unit)
    (i : Fin (2 * t.numNodes + 1)) :
    finiteFactorPaths t ((finSuccEquiv (2 * t.numNodes + 1)).symm (some i)) =
      indexedPath t i := by
  simp [finiteFactorPaths, factorPaths]

#print axioms finiteFactorPaths_outer
#print axioms finiteFactorPaths_vertex

#print axioms mem_indexedPath
#print axioms self_mem_indexedPath
#print axioms root_vertex
#print axioms root_mem_indexedPath
end QuantumNLS.TerraMultiRound53TreeIndex

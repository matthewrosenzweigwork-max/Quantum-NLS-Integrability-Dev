import QuantumNLS.TerraMultiRound54PathSplit

/-! Root/left/right decomposition of the round 53 vertex enumeration. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound54IndexSplit
open QuantumNLS.TerraMultiRound53TreePaths
open QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound54PathSplit

/-- Root and child index sets enumerate all vertices of the parent tree. -/
def splitIndex (l r : BinaryTree Unit) :
    Option (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) →
      Fin (2 * (BinaryTree.node () l r).numNodes + 1)
  | none => rootIndex (.node () l r)
  | some (.inl i) => leftIndex l r i
  | some (.inr i) => rightIndex l r i

theorem splitIndex_injective (l r : BinaryTree Unit) : Function.Injective (splitIndex l r) := by
  intro a b h
  have hv := congrArg (indexedVertex (.node () l r)) h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => cases b <;> simp [splitIndex] at hv
  | some a =>
    cases b with
    | none => cases a <;> simp [splitIndex] at hv
    | some b =>
      cases a with
      | inl i =>
        cases b with
        | inl j =>
          simp only [splitIndex, indexedVertex_left, List.cons.injEq, true_and] at hv
          have := indexedVertex_injective l hv
          simp [this]
        | inr j => simp [splitIndex] at hv
      | inr i =>
        cases b with
        | inl j => simp [splitIndex] at hv
        | inr j =>
          simp only [splitIndex, indexedVertex_right, List.cons.injEq, true_and] at hv
          have := indexedVertex_injective r hv
          simp [this]

theorem splitIndex_surjective (l r : BinaryTree Unit) : Function.Surjective (splitIndex l r) := by
  intro i
  have hv := indexedVertex_mem (.node () l r) i
  generalize he : indexedVertex (.node () l r) i = v at hv
  cases v with
  | nil =>
    refine ⟨none, ?_⟩
    apply indexedVertex_injective (.node () l r)
    simpa [splitIndex] using he.symm
  | cons b v =>
    cases b with
    | false =>
      have hmem : v ∈ vertices l := (mem_vertices_left l r v).mp hv
      let j := vertexIndex l ⟨v, hmem⟩
      have hj : indexedVertex l j = v := by
        change ((vertexIndex l).symm ((vertexIndex l) ⟨v, hmem⟩)).val = v
        rw [Equiv.symm_apply_apply]
      refine ⟨some (.inl j), ?_⟩
      apply indexedVertex_injective (.node () l r)
      simpa [splitIndex, hj] using he.symm
    | true =>
      have hmem : v ∈ vertices r := (mem_vertices_right l r v).mp hv
      let j := vertexIndex r ⟨v, hmem⟩
      have hj : indexedVertex r j = v := by
        change ((vertexIndex r).symm ((vertexIndex r) ⟨v, hmem⟩)).val = v
        rw [Equiv.symm_apply_apply]
      refine ⟨some (.inr j), ?_⟩
      apply indexedVertex_injective (.node () l r)
      simpa [splitIndex, hj] using he.symm

/-- Bijection required to reindex the parent orthant into root, left and
right time coordinates. -/
def splitEquiv (l r : BinaryTree Unit) :
    Option (Fin (2 * l.numNodes + 1) ⊕ Fin (2 * r.numNodes + 1)) ≃
      Fin (2 * (BinaryTree.node () l r).numNodes + 1) :=
  Equiv.ofBijective (splitIndex l r) ⟨splitIndex_injective l r, splitIndex_surjective l r⟩

#print axioms splitIndex_injective
#print axioms splitIndex_surjective
#print axioms splitEquiv
end QuantumNLS.TerraMultiRound54IndexSplit

import QuantumNLS.TerraMultiRound50TreeIntegral

/-! Canonical root-to-vertex addresses for ordered full binary trees. -/
set_option autoImplicit false
namespace QuantumNLS.TerraMultiRound53TreePaths

private def consEmbedding (b : Bool) : List Bool ↪ List Bool where
  toFun := List.cons b
  inj' := by intro x y h; exact (List.cons.inj h).2

/-- The empty address is the root; `false` and `true` select the left and
right subtree respectively. Both internal nodes and leaves are vertices. -/
def vertices : BinaryTree Unit → Finset (List Bool)
  | .nil => {[]}
  | .node _ left right =>
      insert [] ((vertices left).map (consEmbedding false) ∪
                 (vertices right).map (consEmbedding true))

@[simp] theorem root_mem (t : BinaryTree Unit) : [] ∈ vertices t := by
  cases t <;> simp [vertices]

/-- Every ordered full binary tree with `n` internal nodes has `2n+1`
vertices. -/
theorem card_vertices (t : BinaryTree Unit) :
    (vertices t).card = 2 * t.numNodes + 1 := by
  induction t with
  | nil => simp [vertices, BinaryTree.numNodes]
  | node v l r ihl ihr =>
      have hd : Disjoint ((vertices l).map (consEmbedding false))
          ((vertices r).map (consEmbedding true)) := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        simp only [Finset.mem_map] at hx hy
        obtain ⟨a, _, ha⟩ := hx
        obtain ⟨b, _, hb⟩ := hy
        have h := ha.trans hb.symm
        change false :: a = true :: b at h
        cases h
      have hn : [] ∉ ((vertices l).map (consEmbedding false) ∪
          (vertices r).map (consEmbedding true)) := by
        simp [consEmbedding]
      rw [vertices, Finset.card_insert_of_notMem hn, Finset.card_union_of_disjoint hd]
      simp only [Finset.card_map, ihl, ihr, BinaryTree.numNodes]
      omega

/-- The path to a vertex consists of its addresses among the prefixes. -/
def path (t : BinaryTree Unit) (v : List Bool) : Finset (List Bool) :=
  (vertices t).filter (fun w => w <+: v)

@[simp] theorem root_mem_path (t : BinaryTree Unit) (v : List Bool) : [] ∈ path t v := by
  simp [path]

theorem self_mem_path (t : BinaryTree Unit) {v : List Bool} (hv : v ∈ vertices t) :
    v ∈ path t v := by simp [path, hv]

theorem path_subset_vertices (t : BinaryTree Unit) (v : List Bool) :
    path t v ⊆ vertices t := Finset.filter_subset _ _

#print axioms card_vertices
#print axioms root_mem_path
#print axioms self_mem_path
#print axioms path_subset_vertices
end QuantumNLS.TerraMultiRound53TreePaths

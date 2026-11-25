/-
QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound37 — additive
zero-overlap symmetry attempt for LOCAL-011.
-/
import QuantumNLS.PlacementFiberPrefixCommutatorAssembly

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberPrefixCommutator
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.RootOverlapCommutator QuantumNLS.PlacementGrouping

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound37

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem zeroOverlapSlotEquiv_symm (p q : ℕ) :
    overlapSlotEquiv (Nat.zero_le p) (Nat.zero_le q) =
      (overlapSlotEquiv (Nat.zero_le q) (Nat.zero_le p)).symm := by
  ext x
  rfl

/-- Swapping the disjoint subsets gives an equivalence of the two finite
zero-overlap configuration types. -/
private def zeroOverlapConfigurationEquiv (p q : ℕ) :
    OverlapConfiguration p q 0 (Nat.zero_le p) (Nat.zero_le q) ≃
      OverlapConfiguration q p 0 (Nat.zero_le q) (Nat.zero_le p) where
  toFun C := by
    let e := overlapSlotEquiv (Nat.zero_le q) (Nat.zero_le p)
    let f := overlapSlotEquiv (Nat.zero_le p) (Nat.zero_le q)
    have hef : f = e.symm := zeroOverlapSlotEquiv_symm p q
    have hdisj : Disjoint C.left.1 (C.right.1.map f.toEmbedding) := by
      apply Finset.disjoint_iff_inter_eq_empty.mpr
      apply Finset.card_eq_zero.mp
      simpa [f, unionSize] using C.overlap_card
    have hnew : Disjoint C.right.1 (C.left.1.map e.toEmbedding) := by
      apply Finset.disjoint_left.mpr
      intro x hxR hxL
      obtain ⟨y, hyL, hyx⟩ := Finset.mem_map.mp hxL
      have hfy : f x = y := by
        calc
          f x = f (e.toEmbedding y) := congrArg f hyx.symm
          _ = y := by simp [hef]
      exact (Finset.disjoint_left.mp hdisj) hyL
        (Finset.mem_map.mpr ⟨x, hxR, hfy⟩)
    have hcard :
        (C.right.1 ∪ C.left.1.map e.toEmbedding).card = q + p := by
      rw [Finset.card_union_of_disjoint hnew, Finset.card_map]
      simp [C.left.2, C.right.2]
    refine ⟨C.right, C.left, ?_, ?_⟩
    · apply Finset.card_eq_zero.mpr
      exact Finset.disjoint_iff_inter_eq_empty.mp hnew
    · apply (C.right.1 ∪ C.left.1.map e.toEmbedding).card_eq_iff_eq_univ.mp
      simpa using hcard
  invFun C := by
    let e := overlapSlotEquiv (Nat.zero_le p) (Nat.zero_le q)
    let f := overlapSlotEquiv (Nat.zero_le q) (Nat.zero_le p)
    have hef : f = e.symm := zeroOverlapSlotEquiv_symm q p
    have hdisj : Disjoint C.left.1 (C.right.1.map f.toEmbedding) := by
      apply Finset.disjoint_iff_inter_eq_empty.mpr
      apply Finset.card_eq_zero.mp
      simpa [f, unionSize] using C.overlap_card
    have hnew : Disjoint C.right.1 (C.left.1.map e.toEmbedding) := by
      apply Finset.disjoint_left.mpr
      intro x hxR hxL
      obtain ⟨y, hyL, hyx⟩ := Finset.mem_map.mp hxL
      have hfy : f x = y := by
        calc
          f x = f (e.toEmbedding y) := congrArg f hyx.symm
          _ = y := by simp [hef]
      exact (Finset.disjoint_left.mp hdisj) hyL
        (Finset.mem_map.mpr ⟨x, hxR, hfy⟩)
    have hcard :
        (C.right.1 ∪ C.left.1.map e.toEmbedding).card = p + q := by
      rw [Finset.card_union_of_disjoint hnew, Finset.card_map]
      simp [C.left.2, C.right.2]
    refine ⟨C.right, C.left, ?_, ?_⟩
    · apply Finset.card_eq_zero.mpr
      exact Finset.disjoint_iff_inter_eq_empty.mp hnew
    · apply (C.right.1 ∪ C.left.1.map e.toEmbedding).card_eq_iff_eq_univ.mp
      simpa using hcard
  left_inv C := by
    cases C
    rfl
  right_inv C := by
    cases C
    rfl

theorem zeroOverlapConfiguration_card_symm (p q : ℕ) :
    Fintype.card (OverlapConfiguration p q 0 (Nat.zero_le p) (Nat.zero_le q)) =
      Fintype.card (OverlapConfiguration q p 0 (Nat.zero_le q) (Nat.zero_le p)) :=
  Fintype.card_congr (zeroOverlapConfigurationEquiv p q)

/-- The exact per-configuration operator transport still needed to turn the
proved swap of finite zero-overlap configurations into kernel symmetry. -/
def ZeroOverlapFusionSwapStatement : Prop :=
  ∀ {p q : ℕ}
    (C : OverlapConfiguration p q 0 (Nat.zero_le p) (Nat.zero_le q))
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q),
    castSymSectorOperator
        (show unionSize p q 0 = unionSize q p 0 from by
          dsimp [unionSize]
          omega).symm
        (overlapFusionKernel (zeroOverlapConfigurationEquiv p q C) Bop A) =
      overlapFusionKernel C A Bop

#print axioms zeroOverlapSlotEquiv_symm
#print axioms zeroOverlapConfigurationEquiv
#print axioms zeroOverlapConfiguration_card_symm
#print axioms ZeroOverlapFusionSwapStatement

end QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound37

end

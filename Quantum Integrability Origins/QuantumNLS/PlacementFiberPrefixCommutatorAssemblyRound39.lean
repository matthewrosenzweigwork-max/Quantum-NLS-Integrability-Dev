/-
QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound39 — finite zero-overlap
average reindexing after the frozen Round38 per-configuration transport.
-/
import QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound38

set_option linter.style.haveILetI false

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberPrefixCommutator
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound37
  QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound38

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound39

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem zeroOverlapSlotEquiv_symm (p q : ℕ) :
    overlapSlotEquiv (Nat.zero_le p) (Nat.zero_le q) =
      (overlapSlotEquiv (Nat.zero_le q) (Nat.zero_le p)).symm := by
  ext x
  rfl

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

omit [CompleteSpace H] in
private theorem castSymSectorOperator_smul_sum {m n : ℕ} (h : m = n)
    {ι : Type*} [Fintype ι] (c : ℂ)
    (F : ι → SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    castSymSectorOperator h (c • ∑ i, F i) =
      c • ∑ i, castSymSectorOperator h (F i) := by
  cases h
  rfl

omit [CompleteSpace H] in
private theorem castSymSectorOperator_sum {m n : ℕ} (h : m = n)
    {ι : Type*} [Fintype ι]
    (F : ι → SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    castSymSectorOperator h (∑ i, F i) =
      ∑ i, castSymSectorOperator h (F i) := by
  cases h
  rfl

/-- The zero-overlap kernel averages are symmetric, with the size equality
proved internally and no compatibility premise. -/
theorem zeroOverlapKernelIdentity :
    ZeroOverlapKernelIdentity (H := H) := by
  classical
  intro p q A Bop
  let h : unionSize p q 0 = unionSize q p 0 := by
    dsimp [unionSize]
    omega
  let E := zeroOverlapConfigurationEquiv p q
  letI : Fintype (OverlapConfiguration p q 0
      (Nat.zero_le p) (Nat.zero_le q)) := Fintype.ofFinite _
  letI : Fintype (OverlapConfiguration q p 0
      (Nat.zero_le q) (Nat.zero_le p)) := Fintype.ofFinite _
  have hcardN :=
    zeroOverlapConfiguration_card_symm p q
  have hcard :
      (Fintype.card (OverlapConfiguration p q 0
        (Nat.zero_le p) (Nat.zero_le q)) : ℂ) =
      (Fintype.card (OverlapConfiguration q p 0
        (Nat.zero_le q) (Nat.zero_le p)) : ℂ) := by
    exact_mod_cast hcardN
  have hsum :
      (∑ D : OverlapConfiguration q p 0
          (Nat.zero_le q) (Nat.zero_le p),
        castSymSectorOperator h.symm (overlapFusionKernel D Bop A)) =
        ∑ C : OverlapConfiguration p q 0
            (Nat.zero_le p) (Nat.zero_le q),
          overlapFusionKernel C A Bop := by
    have hsize : p + q = q + p := by simpa [unionSize] using h
    have hEq : h = hsize := Subsingleton.elim _ _
    have hcastPointwise :
        ∀ C : OverlapConfiguration p q 0
            (Nat.zero_le p) (Nat.zero_le q),
          castSymSectorOperator hsize.symm
              (overlapFusionKernel (E C) Bop A) =
            overlapFusionKernel C A Bop := by
      intro C
      have hpoint := zeroOverlapFusionKernel_swap (H := H) C A Bop
      change castSymSectorOperator hsize.symm
          (overlapFusionKernel (E C) Bop A) =
        overlapFusionKernel C A Bop at hpoint
      exact hpoint
    calc
      _ = ∑ C : OverlapConfiguration p q 0
            (Nat.zero_le p) (Nat.zero_le q),
          castSymSectorOperator hsize.symm
            (overlapFusionKernel (E C) Bop A) := by
              symm
              exact Equiv.sum_comp E
                (fun D => castSymSectorOperator hsize.symm
                  (overlapFusionKernel D Bop A))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro C hC
        exact hcastPointwise C
  have hsize : p + q = q + p := by simpa [unionSize] using h
  have hEq : h = hsize := Subsingleton.elim _ _
  have hcastSum :
      castSymSectorOperator hsize.symm
          (∑ D : OverlapConfiguration q p 0
            (Nat.zero_le q) (Nat.zero_le p), overlapFusionKernel D Bop A) =
        ∑ C : OverlapConfiguration p q 0
            (Nat.zero_le p) (Nat.zero_le q), overlapFusionKernel C A Bop := by
    rw [castSymSectorOperator_sum]
    exact hsum
  have hcastAverage :
      castSymSectorOperator hsize.symm
          (((Fintype.card (OverlapConfiguration q p 0
              (Nat.zero_le q) (Nat.zero_le p)) : ℂ)⁻¹) •
            ∑ D : OverlapConfiguration q p 0
              (Nat.zero_le q) (Nat.zero_le p),
              overlapFusionKernel D Bop A) =
        ((Fintype.card (OverlapConfiguration p q 0
            (Nat.zero_le p) (Nat.zero_le q)) : ℂ)⁻¹) •
          ∑ C : OverlapConfiguration p q 0
            (Nat.zero_le p) (Nat.zero_le q),
            overlapFusionKernel C A Bop := by
    rw [castSymSectorOperator_smul_sum]
    rw [hcard]
    exact congrArg
      (fun T =>
        ((Fintype.card (OverlapConfiguration q p 0
            (Nat.zero_le q) (Nat.zero_le p)) : ℂ)⁻¹) • T)
      hsum
  rw [averagedOverlapKernel_eq_average (Nat.zero_le p) (Nat.zero_le q) A Bop,
    averagedOverlapKernel_eq_average (Nat.zero_le q) (Nat.zero_le p) Bop A]
  exact hcastAverage.symm

#print axioms zeroOverlapKernelIdentity

end QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound39

end

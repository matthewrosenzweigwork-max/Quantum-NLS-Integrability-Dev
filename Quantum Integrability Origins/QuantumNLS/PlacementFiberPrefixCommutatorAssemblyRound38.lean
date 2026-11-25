/-
QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound38 — zero-overlap
fusion-kernel transport, continuing the frozen Round37 checkpoint.
-/
import QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound37

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberPrefixCommutator
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound37
  QuantumNLS.RootOverlapCommutator QuantumNLS.PlacementGrouping

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound38

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- Transport a compressed tensor operator along an arbitrary equality of
sector sizes.  The index is generalized before eliminating the equality, so
the dependent sector coercion is never rewritten beneath the operator. -/
theorem castSymSectorOperator_compression {m n : ℕ} (h : m = n)
    (T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) :
    castSymSectorOperator h
      ((symProjToSector m).comp
        (T.comp (SymSector ℂ H m).subtypeL)) =
      (symProjToSector n).comp
        ((castTensorOperator h T).comp (SymSector ℂ H n).subtypeL) := by
  cases h
  rfl

omit [CompleteSpace H] in
private theorem castTensorOperator_comp {m n : ℕ} (h : m = n)
    (X Y : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) :
    castTensorOperator h (X.comp Y) =
      (castTensorOperator h X).comp (castTensorOperator h Y) := by
  cases h
  rfl

omit [CompleteSpace H] in
private theorem castTensorOperator_trans {m n l : ℕ}
    (h : m = n) (g : n = l)
    (T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) :
    castTensorOperator g (castTensorOperator h T) =
      castTensorOperator (h.trans g) T := by
  cases h
  cases g
  rfl

omit [CompleteSpace H] in
private theorem castSubsetPlacement_eq_of_slots {N p q m : ℕ}
    (h₁ : p + q = N) (h₂ : p + m = N) (hp : p ≤ N)
    (S : PlacementSubset p q) (T : PlacementSubset p m)
    (hslots : castSlotSet h₁ S.1 = castSlotSet h₂ T.1)
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    castTensorOperator h₁ (subsetPlacement S A) =
      castTensorOperator h₂ (subsetPlacement T A) := by
  have hsource₁ : castTensorOperator h₁ (subsetPlacement S A) =
      castTensorOperator (Nat.add_sub_of_le hp)
        (subsetPlacement
          (sourcePlacementOfSlots hp (castSlotSet h₁ S.1)
            (by simpa [castSlotSet] using S.2)) A) := by
    have hq : q = N - p := by omega
    subst q
    have hh : h₁ = Nat.add_sub_of_le hp := Subsingleton.elim _ _
    have hS : sourcePlacementOfSlots hp (castSlotSet h₁ S.1)
        (by simpa [castSlotSet] using S.2) = S := by
      apply Subtype.ext
      change castSlotSet (Nat.add_sub_of_le hp).symm
          (castSlotSet h₁ S.1) = S.1
      rw [hh]
      exact castSlotSet_symm _ _
    rw [hh, hS]
  have hsource₂ : castTensorOperator h₂ (subsetPlacement T A) =
      castTensorOperator (Nat.add_sub_of_le hp)
        (subsetPlacement
          (sourcePlacementOfSlots hp (castSlotSet h₂ T.1)
            (by simpa [castSlotSet] using T.2)) A) := by
    have hm : m = N - p := by omega
    subst m
    have hh : h₂ = Nat.add_sub_of_le hp := Subsingleton.elim _ _
    have hT : sourcePlacementOfSlots hp (castSlotSet h₂ T.1)
        (by simpa [castSlotSet] using T.2) = T := by
      apply Subtype.ext
      change castSlotSet (Nat.add_sub_of_le hp).symm
          (castSlotSet h₂ T.1) = T.1
      rw [hh]
      exact castSlotSet_symm _ _
    rw [hh, hT]
  rw [hsource₁, hsource₂]
  congr 2
  apply Subtype.ext
  exact congrArg (castSlotSet (Nat.add_sub_of_le hp).symm) hslots

private theorem zeroOverlapSlotEquiv_symm (p q : ℕ) :
    overlapSlotEquiv (Nat.zero_le p) (Nat.zero_le q) =
      (overlapSlotEquiv (Nat.zero_le q) (Nat.zero_le p)).symm := by
  ext x
  rfl

/-- The swap equivalence on the finite zero-overlap configuration spaces.
The subset data is swapped, with its right slots transported by the inverse
zero-overlap slot equivalence. -/
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

/-- The exact per-configuration zero-overlap fusion transport.  The tensor
operators are first transported through the arbitrary sector equality, then
the frozen disjoint-placement commutation theorem swaps their order. -/
theorem zeroOverlapFusionKernel_swap {p q : ℕ}
    (C : OverlapConfiguration p q 0 (Nat.zero_le p) (Nat.zero_le q))
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    castSymSectorOperator
        (show unionSize p q 0 = unionSize q p 0 from by
          dsimp [unionSize]
          omega).symm
        (overlapFusionKernel (zeroOverlapConfigurationEquiv p q C) Bop A) =
      overlapFusionKernel C A Bop := by
  classical
  let h : unionSize p q 0 = unionSize q p 0 := by
    dsimp [unionSize]
    omega
  change castSymSectorOperator h.symm
      (overlapFusionKernel (zeroOverlapConfigurationEquiv p q C) Bop A) =
    overlapFusionKernel C A Bop
  let e := overlapSlotEquiv (Nat.zero_le p) (Nat.zero_le q)
  let Rslots : Finset (Fin (p + q)) := C.right.1.map e.toEmbedding
  have hp : p ≤ p + q := by omega
  have hq : q ≤ p + q := by omega
  have hRcard : Rslots.card = q := by
    simp [Rslots, C.right.2]
  let SL : PlacementSubset p ((p + q) - p) :=
    sourcePlacementOfSlots hp C.left.1 (by simpa using C.left.2)
  let TL : PlacementSubset q ((p + q) - q) :=
    sourcePlacementOfSlots hq Rslots hRcard
  let z : ActualPairPlacement (p + q) p q := (SL, TL)
  have hleftSlots : leftSlots hp z = C.left.1 := by
    simpa [z, SL, leftSlots] using
      (slots_sourcePlacementOfSlots hp C.left.1 (by simpa using C.left.2))
  have hrightSlots : rightSlots hq z = Rslots := by
    simpa [z, TL, rightSlots] using
      (slots_sourcePlacementOfSlots hq Rslots hRcard)
  have hzero : (C.left.1 ∩ Rslots).card = 0 := by
    simpa [Rslots, e, unionSize] using C.overlap_card
  have hlocalDisj : Disjoint C.left.1 Rslots :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero)
  have hzdisj : Disjoint (leftSlots hp z) (rightSlots hq z) := by
    rw [hleftSlots, hrightSlots]
    exact hlocalDisj
  have hcomm := rawPlacement_commute_of_disjoint (p + q) p q hp hq A Bop z hzdisj
  have hleftSlotsCast :
      castSlotSet (Nat.add_sub_of_le hp) SL.1 =
        castSlotSet (show p + (q - 0) = p + q by simp) C.left.1 := by
    have hh : (show p + (q - 0) = p + q by simp) = rfl := Subsingleton.elim _ _
    rw [hh]
    simpa [castSlotSet] using
      (slots_sourcePlacementOfSlots hp C.left.1 (by simpa using C.left.2))
  have hleftRaw :
      rawSubsetPlacement (p + q) p hp SL A = subsetPlacement C.left A := by
    change castTensorOperator (Nat.add_sub_of_le hp) (subsetPlacement SL A) =
      castTensorOperator (show p + (q - 0) = p + q by simp)
        (subsetPlacement C.left A)
    rw [castSubsetPlacement_eq_of_slots
      (Nat.add_sub_of_le hp) (show p + (q - 0) = p + q by simp)
      hp SL C.left hleftSlotsCast A]
  have hrightLocal : q + (p - 0) = p + (q - 0) := by omega
  have hrightSlotsCast :
      castSlotSet (Nat.add_sub_of_le hq) TL.1 =
        castSlotSet hrightLocal C.right.1 := by
    calc
      _ = Rslots := by
        simpa [TL] using
          (slots_sourcePlacementOfSlots hq Rslots hRcard)
      _ = castSlotSet hrightLocal C.right.1 := by
        change C.right.1.map e.toEmbedding =
          C.right.1.map (Equiv.cast (congrArg Fin hrightLocal)).toEmbedding
        have he : e = Equiv.cast (congrArg Fin hrightLocal) := by
          unfold e overlapSlotEquiv
          congr 1
        rw [he]
  have hrightRaw :
      rawSubsetPlacement (p + q) q hq TL Bop = rightPlacement C Bop := by
    change castTensorOperator (Nat.add_sub_of_le hq) (subsetPlacement TL Bop) =
      castTensorOperator hrightLocal (subsetPlacement C.right Bop)
    exact castSubsetPlacement_eq_of_slots
      (Nat.add_sub_of_le hq) hrightLocal hq TL C.right hrightSlotsCast Bop
  have hcommLocal :
      (subsetPlacement C.left A).comp (rightPlacement C Bop) =
        (rightPlacement C Bop).comp (subsetPlacement C.left A) := by
    rw [← hleftRaw, ← hrightRaw]
    simpa [z] using hcomm
  have hsize : p + q = q + p := by simpa [unionSize] using h
  let C' := zeroOverlapConfigurationEquiv p q C
  have hswapLeft :
      castTensorOperator h.symm (subsetPlacement C'.left Bop) =
        rightPlacement C Bop := by
    change castTensorOperator h.symm (subsetPlacement C.right Bop) =
      castTensorOperator hrightLocal (subsetPlacement C.right Bop)
    congr 1
  have hswapRight :
      castTensorOperator h.symm (rightPlacement C' A) =
        subsetPlacement C.left A := by
    have hswapDim : p + (q - 0) = unionSize q p 0 := by
      dsimp [unionSize]
      omega
    change castTensorOperator h.symm
        (castTensorOperator hswapDim (subsetPlacement C.left A)) =
      subsetPlacement C.left A
    rw [castTensorOperator_trans hswapDim h.symm]
    have hid : hswapDim.trans h.symm = rfl := Subsingleton.elim _ _
    rw [hid]
    rfl
  have hcastProd :
      castTensorOperator h.symm
          ((subsetPlacement C'.left Bop).comp (rightPlacement C' A)) =
        (castTensorOperator h.symm (subsetPlacement C'.left Bop)).comp
          (castTensorOperator h.symm (rightPlacement C' A)) :=
    castTensorOperator_comp h.symm _ _
  have hEq : h = hsize := Subsingleton.elim _ _
  have he : h.symm = hsize.symm := congrArg Eq.symm hEq
  have hcastProdSize :
      castTensorOperator hsize.symm
          ((subsetPlacement C'.left Bop).comp (rightPlacement C' A)) =
        (castTensorOperator hsize.symm (subsetPlacement C'.left Bop)).comp
          (castTensorOperator hsize.symm (rightPlacement C' A)) :=
    castTensorOperator_comp hsize.symm _ _
  have hswapLeftSize :
      castTensorOperator hsize.symm (subsetPlacement C'.left Bop) =
        rightPlacement C Bop := by
    rw [← he]
    exact hswapLeft
  have hswapRightSize :
      castTensorOperator hsize.symm (rightPlacement C' A) =
        subsetPlacement C.left A := by
    rw [← he]
    exact hswapRight
  rw [hEq]
  change castSymSectorOperator hsize.symm
      ((symProjToSector (q + p)).comp
        (((subsetPlacement C'.left Bop).comp (rightPlacement C' A)).comp
          (SymSector ℂ H (q + p)).subtypeL)) =
    (symProjToSector (p + q)).comp
      (((subsetPlacement C.left A).comp (rightPlacement C Bop)).comp
        (SymSector ℂ H (p + q)).subtypeL)
  rw [castSymSectorOperator_compression hsize.symm, hcastProdSize,
    hswapLeftSize, hswapRightSize]
  change (symProjToSector (p + (q - 0))).comp
      (((rightPlacement C Bop).comp (subsetPlacement C.left A)).comp
        (SymSector ℂ H (p + (q - 0))).subtypeL) =
    (symProjToSector (p + (q - 0))).comp
      (((subsetPlacement C.left A).comp (rightPlacement C Bop)).comp
        (SymSector ℂ H (p + (q - 0))).subtypeL)
  exact congrArg
    (fun T : HilbertTensorPower ℂ H (p + (q - 0)) →L[ℂ]
        HilbertTensorPower ℂ H (p + (q - 0)) =>
      (symProjToSector (p + (q - 0))).comp
        (T.comp (SymSector ℂ H (p + (q - 0))).subtypeL)) hcommLocal.symm

#print axioms castSymSectorOperator_compression
#print axioms zeroOverlapFusionKernel_swap

end QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound38

end

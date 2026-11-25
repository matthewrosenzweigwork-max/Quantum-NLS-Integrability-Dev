/-
QuantumNLS.PlacementFiberCanonicalPrefix — canonical-prefix comparison for
the globally compressed union-fiber average in LOCAL-011.

All prior placement, transport, operator, grouping, and fixed-degree bound
modules are imported read-only. This module proves local and ambient fiber
transitivity, permutation invariance of the globally compressed terms, and
constancy of each normalized fiber average at its canonical representative.
The remaining prefix-placement comparison is recorded as an exact `Prop`;
the product and radius assembly depend on closing it.
-/
import QuantumNLS.PlacementFiberBound

set_option maxHeartbeats 5000000

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberGrouping
  QuantumNLS.PlacementFiberBound

noncomputable section

namespace QuantumNLS.PlacementFiberCanonicalPrefix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The canonical embedding of the first `r` ambient slots. -/
def canonicalPrefixEmbedding {N r : ℕ} (hr : r ≤ N) : Fin r ↪ Fin N :=
  Fin.castLEEmb hr

/-- The ambient subset selected by the canonical prefix embedding. -/
def canonicalPrefixSlots {N r : ℕ} (hr : r ≤ N) : Finset (Fin N) :=
  Finset.univ.map (canonicalPrefixEmbedding hr)

theorem canonicalPrefixSlots_card {N r : ℕ} (hr : r ≤ N) :
    (canonicalPrefixSlots hr).card = r := by
  simp [canonicalPrefixSlots]

theorem canonicalPrefixPairBase_slots {N p q : ℕ}
    (b : PairPlacementBase N p q) :
    (canonicalPrefixPairBase b).1.2 =
      canonicalPrefixSlots (pairPlacementBase_unionSize_le_N b) := by
  ext i
  simp [canonicalPrefixPairBase, canonicalPrefixSlots,
    canonicalPrefixEmbedding]

abbrev PairSlotColor := Bool × Bool

private def localRightSlots {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq) : Finset (Fin (p + (q - s))) :=
  C.right.1.map (overlapSlotEquiv hsp hsq).toEmbedding

private def localPairColor {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq) (i : Fin (p + (q - s))) : PairSlotColor :=
  (i ∈ C.left.1, i ∈ localRightSlots hsp hsq C)

private def localPairColorSet {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq) (c : PairSlotColor) :
    Finset (Fin (p + (q - s))) :=
  Finset.univ.filter (fun i => localPairColor hsp hsq C i = c)

private theorem localPairColorSet_eq {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq) :
    localPairColorSet hsp hsq C (true, true) = C.left.1 ∩ localRightSlots hsp hsq C ∧
    localPairColorSet hsp hsq C (true, false) = C.left.1 \ localRightSlots hsp hsq C ∧
    localPairColorSet hsp hsq C (false, true) = localRightSlots hsp hsq C \ C.left.1 ∧
    localPairColorSet hsp hsq C (false, false) =
      Finset.univ \ (C.left.1 ∪ localRightSlots hsp hsq C) := by
  constructor
  · ext i
    simp [localPairColorSet, localPairColor]
  constructor
  · ext i
    simp [localPairColorSet, localPairColor]
  constructor
  · ext i
    simp [localPairColorSet, localPairColor, and_comm]
  · ext i
    simp [localPairColorSet, localPairColor]

private theorem localPairColorSet_card {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq) (c : PairSlotColor) :
    (localPairColorSet hsp hsq C c).card =
      (match c with
       | (true, true) => s
       | (true, false) => p - s
       | (false, true) => q - s
       | (false, false) => 0) := by
  have hc := localPairColorSet_eq hsp hsq C
  have hright : (localRightSlots hsp hsq C).card = q := by
    simp [localRightSlots, C.right.2]
  have hI : (C.left.1 ∩ localRightSlots hsp hsq C).card = s := by
    exact C.overlap_card
  have hboth : (localPairColorSet hsp hsq C (true, true)).card = s := by
    rw [hc.1]
    exact C.overlap_card
  have hleftOnly :
      (localPairColorSet hsp hsq C (true, false)).card = p - s := by
    rw [hc.2.1, Finset.card_sdiff, C.left.2, Finset.inter_comm, hI]
  have hrightOnly :
      (localPairColorSet hsp hsq C (false, true)).card = q - s := by
    rw [hc.2.2.1, Finset.card_sdiff, hright, hI]
  have hneither :
      (localPairColorSet hsp hsq C (false, false)).card = 0 := by
    have hcov : C.left.1 ∪ localRightSlots hsp hsq C = Finset.univ := by
      simpa [localRightSlots] using C.covers_union
    rw [hc.2.2.2, hcov]
    simp
  rcases c with ⟨a, b⟩
  cases a <;> cases b
  · exact hneither
  · exact hrightOnly
  · exact hleftOnly
  · exact hboth

private theorem localPairColorSubtype_card {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq) (c : PairSlotColor) :
    Fintype.card {i : Fin (p + (q - s)) // localPairColor hsp hsq C i = c} =
      (localPairColorSet hsp hsq C c).card := by
  rw [Fintype.card_subtype]
  rfl

private theorem localRightSlots_relabel {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (σ : Equiv.Perm (Fin (p + (q - s))))
    (C : OverlapConfiguration p q s hsp hsq) :
    localRightSlots hsp hsq (relabelOverlapConfiguration hsp hsq σ C) =
      (localRightSlots hsp hsq C).map σ.toEmbedding := by
  let e := overlapSlotEquiv hsp hsq
  let hqr := canonicalRightDimensionEq p q s hsp hsq
  have htransport (x : Fin (q + (p - s))) :
      e (castPermBack hqr σ x) = σ (e x) := by
    simp [e, castPermBack, overlapSlotEquiv]
  dsimp [localRightSlots, relabelOverlapConfiguration]
  rw [Finset.map_map, Finset.map_map]
  congr 1
  ext x
  exact congrArg Fin.val (htransport x)

/-- Slot permutations act transitively on the configurations in one
fixed-union/fixed-overlap fiber. The four membership classes have sizes
`s`, `p-s`, `q-s`, and zero, so a fiberwise equivalence gives the required
permutation. -/
theorem exists_relabelOverlapConfiguration_eq {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (C D : OverlapConfiguration p q s hsp hsq) :
    ∃ σ : Equiv.Perm (Fin (p + (q - s))),
      C.left.1.map σ.toEmbedding = D.left.1 ∧
        (localRightSlots hsp hsq C).map σ.toEmbedding =
          localRightSlots hsp hsq D := by
  let colorC := localPairColor hsp hsq C
  let colorD := localPairColor hsp hsq D
  have hcard (c : PairSlotColor) :
      Fintype.card {i : Fin (p + (q - s)) // colorC i = c} =
        Fintype.card {i : Fin (p + (q - s)) // colorD i = c} := by
    rw [localPairColorSubtype_card, localPairColorSet_card,
      localPairColorSubtype_card, localPairColorSet_card]
  let fiberEquiv : ∀ c : PairSlotColor,
      {i : Fin (p + (q - s)) // colorC i = c} ≃
        {i : Fin (p + (q - s)) // colorD i = c} := by
    intro c
    exact (Fintype.equivFin _).trans
      ((Equiv.cast (congrArg Fin (hcard c))).trans (Fintype.equivFin _).symm)
  let σ : Equiv.Perm (Fin (p + (q - s))) := Equiv.ofFiberEquiv fiberEquiv
  have hcolor (i : Fin (p + (q - s))) : colorD (σ i) = colorC i :=
    Equiv.ofFiberEquiv_map fiberEquiv i
  have hleftMem (i : Fin (p + (q - s))) :
      (i ∈ C.left.1) ↔ (σ i ∈ D.left.1) := by
    have h := congrArg Prod.fst (hcolor i)
    simpa [colorC, colorD, localPairColor] using h.symm
  have hrightMem (i : Fin (p + (q - s))) :
      (i ∈ localRightSlots hsp hsq C) ↔
        (σ i ∈ localRightSlots hsp hsq D) := by
    have h := congrArg Prod.snd (hcolor i)
    simpa [colorC, colorD, localPairColor] using h.symm
  have hleft : C.left.1.map σ.toEmbedding = D.left.1 := by
    ext j
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hleftMem i |>.mp hi
    · intro hj
      refine ⟨σ.symm j, ?_, by simp⟩
      exact hleftMem (σ.symm j) |>.mpr (by simpa using hj)
  have hright :
      (localRightSlots hsp hsq C).map σ.toEmbedding =
        localRightSlots hsp hsq D := by
    ext j
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hrightMem i |>.mp hi
    · intro hj
      refine ⟨σ.symm j, ?_, by simp⟩
      exact hrightMem (σ.symm j) |>.mpr (by simpa using hj)
  exact ⟨σ, hleft, hright⟩

/-- The locally compressed ordered product is invariant under simultaneous
slot relabelling. This is the frozen symmetric-compression covariance
applied after the two placement-transport identities. -/
theorem overlapFusionKernel_relabel {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (σ : Equiv.Perm (Fin (p + (q - s))))
    (C : OverlapConfiguration p q s hsp hsq)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    overlapFusionKernel (relabelOverlapConfiguration hsp hsq σ C) A Bop =
      overlapFusionKernel C A Bop := by
  let U : HilbertTensorPower ℂ H (p + (q - s)) →L[ℂ]
      HilbertTensorPower ℂ H (p + (q - s)) := permRep ℂ H _ σ
  let Ui : HilbertTensorPower ℂ H (p + (q - s)) →L[ℂ]
      HilbertTensorPower ℂ H (p + (q - s)) := permRep ℂ H _ σ⁻¹
  let X := subsetPlacement C.left A
  let Y := rightPlacement C Bop
  have hcancel (x : HilbertTensorPower ℂ H (p + (q - s))) : U (Ui x) = x := by
    change permHilbertIsometry (𝕜 := ℂ) (E := H) σ
        (permHilbertIsometry (𝕜 := ℂ) (E := H) σ⁻¹ x) = x
    have h := map_mul (permHom ℂ H (p + (q - s))) σ σ⁻¹
    calc
      _ = permHilbertIsometry (𝕜 := ℂ) (E := H) (σ * σ⁻¹) x := by
        simpa [permHom] using
          (congrArg (fun f : _ ≃ₗᵢ[ℂ] _ => f x) h).symm
      _ = permHilbertIsometry (𝕜 := ℂ) (E := H) 1 x := by rw [mul_inv_cancel]
      _ = x := by
        have hone := map_one (permHom ℂ H (p + (q - s)))
        simpa [permHom] using
          (congrArg (fun f : _ ≃ₗᵢ[ℂ] _ => f x) hone)
  have hcancelInv (x : HilbertTensorPower ℂ H (p + (q - s))) : Ui (U x) = x := by
    change permHilbertIsometry (𝕜 := ℂ) (E := H) σ⁻¹
        (permHilbertIsometry (𝕜 := ℂ) (E := H) σ x) = x
    have h := map_mul (permHom ℂ H (p + (q - s))) σ⁻¹ σ
    calc
      _ = permHilbertIsometry (𝕜 := ℂ) (E := H) (σ⁻¹ * σ) x := by
        simpa [permHom] using
          (congrArg (fun f : _ ≃ₗᵢ[ℂ] _ => f x) h).symm
      _ = permHilbertIsometry (𝕜 := ℂ) (E := H) 1 x := by rw [inv_mul_cancel]
      _ = x := by
        have hone := map_one (permHom ℂ H (p + (q - s)))
        simpa [permHom] using
          (congrArg (fun f : _ ≃ₗᵢ[ℂ] _ => f x) hone)
  have hleft :
      (U.comp X).comp Ui =
        subsetPlacement (relabelOverlapConfiguration hsp hsq σ C).left A := by
    have hsubset :
        (relabelOverlapConfiguration hsp hsq σ C).left =
          relabelPlacementSubset σ C.left := by
      apply Subtype.ext
      rfl
    rw [hsubset]
    simpa [U, Ui, X] using
      (permutedPlacement_conjugate_subset σ C.left A)
  have hright :
      (U.comp Y).comp Ui =
        rightPlacement (relabelOverlapConfiguration hsp hsq σ C) Bop := by
    simpa [U, Ui, Y] using
      (rightPlacement_relabel_conjugate hsp hsq σ C Bop)
  have hproduct :
      (U.comp (X.comp Y)).comp (Ui.comp (SymSector ℂ H _).subtypeL) =
        ((subsetPlacement (relabelOverlapConfiguration hsp hsq σ C).left A).comp
          (rightPlacement (relabelOverlapConfiguration hsp hsq σ C) Bop)).comp
            (SymSector ℂ H _).subtypeL := by
    ext x
    change U (X (Y (Ui x.1))) = _
    calc
      U (X (Y (Ui x.1))) = ((U.comp X).comp Ui) ((U.comp Y).comp Ui x.1) := by
        simp only [ContinuousLinearMap.comp_apply]
        rw [hcancelInv]
      _ = _ := by
        rw [hleft, hright]
        simp only [ContinuousLinearMap.comp_apply]
        rfl
  calc
    overlapFusionKernel (relabelOverlapConfiguration hsp hsq σ C) A Bop =
        (symProjToSector (p + (q - s))).comp
          (((U.comp (X.comp Y)).comp (Ui.comp (SymSector ℂ H _).subtypeL))) := by
            unfold overlapFusionKernel
            rw [← hproduct]
    _ = overlapFusionKernel C A Bop :=
      PlacementCovariance.symmetricCompression_conj_eq σ (X.comp Y)

private theorem overlapFusionKernel_eq_of_slotSets_eq {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (C D : OverlapConfiguration p q s hsp hsq)
    (hleft : C.left.1 = D.left.1)
    (hright : localRightSlots hsp hsq C = localRightSlots hsp hsq D)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    overlapFusionKernel C A Bop = overlapFusionKernel D A Bop := by
  have hleft' : C.left = D.left := Subtype.ext hleft
  have hrightRaw : C.right.1 = D.right.1 := by
    apply Finset.map_injective (overlapSlotEquiv hsp hsq).toEmbedding
    exact hright
  have hright' : C.right = D.right := Subtype.ext hrightRaw
  simp only [overlapFusionKernel, rightPlacement]
  rw [hleft', hright']

/-- Every concrete local fusion kernel equals its normalized finite
configuration average. The equality follows because the slot-permutation
action is transitive and global symmetric compression erases that action. -/
theorem averagedOverlapKernel_eq_overlapFusionKernel {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    averagedOverlapKernel hsp hsq A Bop = overlapFusionKernel C A Bop := by
  have hconstant :
      (∑ D : OverlapConfiguration p q s hsp hsq,
        overlapFusionKernel D A Bop) =
      (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ) •
        overlapFusionKernel C A Bop := by
    calc
      _ = ∑ _D : OverlapConfiguration p q s hsp hsq,
            overlapFusionKernel C A Bop := by
          apply Finset.sum_congr rfl
          intro D hD
          obtain ⟨σ, hleft, hright⟩ :=
            exists_relabelOverlapConfiguration_eq hsp hsq C D
          have hK := overlapFusionKernel_relabel hsp hsq σ C A Bop
          have hrel := overlapFusionKernel_eq_of_slotSets_eq hsp hsq
            (relabelOverlapConfiguration hsp hsq σ C) D
            (by simpa [relabelOverlapConfiguration] using hleft)
            (by rw [localRightSlots_relabel]; exact hright) A Bop
          exact hrel.symm.trans hK
      _ = (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ) •
            overlapFusionKernel C A Bop := by
          rw [Finset.sum_const, Finset.card_univ,
            ← Nat.cast_smul_eq_nsmul ℂ]
  have hcardmul := localCompressedOverlapSum_eq_card_smul_averagedOverlapKernel
    hsp hsq A Bop
  have hsum :
      (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ) •
          averagedOverlapKernel hsp hsq A Bop =
        (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ) •
          overlapFusionKernel C A Bop := by
    calc
      _ = ∑ D : OverlapConfiguration p q s hsp hsq,
            overlapFusionKernel D A Bop := hcardmul.symm
      _ = (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ) •
            overlapFusionKernel C A Bop := hconstant
  have hn : (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ) ≠ 0 := by
    rw [card_overlapConfiguration]
    exact_mod_cast Nat.ne_of_gt (Nat.mul_pos
      (Nat.choose_pos (show p ≤ p + (q - s) by omega))
      (Nat.choose_pos hsp))
  have hleftCan : averagedOverlapKernel hsp hsq A Bop =
      (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ)⁻¹ •
        ((Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ) •
          averagedOverlapKernel hsp hsq A Bop) := by
    rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hmid :
      (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ)⁻¹ •
          ((Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ) •
            averagedOverlapKernel hsp hsq A Bop) =
        (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ)⁻¹ •
          ((Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ) •
            overlapFusionKernel C A Bop) :=
    congrArg (fun T : BoundedSymmetricKernel H (p + (q - s)) =>
      (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ)⁻¹ • T) hsum
  have hrightCan :
      (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ)⁻¹ •
          ((Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ) •
            overlapFusionKernel C A Bop) = overlapFusionKernel C A Bop := by
    rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
  exact hleftCan.trans (hmid.trans hrightCan)

private theorem pushUnionSlots_relabel {N r : ℕ} (U : Finset (Fin N))
    (hU : U.card = r) (σ : Equiv.Perm (Fin N))
    (τ : Equiv.Perm (Fin r))
    (hστ : ∀ i : Fin r,
      σ (unionSlotEmbedding U hU i) = unionSlotEmbedding U hU (τ i))
    (S : Finset (Fin r)) :
    (pushUnionSlots U hU S).map σ.toEmbedding =
      pushUnionSlots U hU (S.map τ.toEmbedding) := by
  dsimp [pushUnionSlots]
  rw [Finset.map_map, Finset.map_map]
  congr 1
  ext i
  exact congrArg Fin.val (hστ i)

private theorem actualPair_eq_of_slot_sets_eq {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N)
    (z z' : ActualPairPlacement N p q)
    (hleft : leftSlots hp z = leftSlots hp z')
    (hright : rightSlots hq z = rightSlots hq z') : z = z' := by
  apply Prod.ext
  · apply Subtype.ext
    apply Finset.map_injective (Equiv.cast
      (congrArg Fin (Nat.add_sub_of_le hp))).toEmbedding
    exact hleft
  · apply Subtype.ext
    apply Finset.map_injective (Equiv.cast
      (congrArg Fin (Nat.add_sub_of_le hq))).toEmbedding
    exact hright

private theorem canonicalToAmbientPair_eq_of_slotSets_eq {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (C D : OverlapConfiguration p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b))
    (hleft : C.left.1 = D.left.1)
    (hright : localRightSlots (overlapLeftBound b) (overlapRightBound b) C =
      localRightSlots (overlapLeftBound b) (overlapRightBound b) D) :
    canonicalToAmbientPair hp hq b C = canonicalToAmbientPair hp hq b D := by
  apply actualPair_eq_of_slot_sets_eq hp hq
  · rw [canonicalToAmbientPair_leftSlots, canonicalToAmbientPair_leftSlots]
    exact congrArg (pushUnionSlots b.1.2
      (by simpa [overlapSizeOfBase, unionSize] using b.2)) hleft
  · rw [canonicalToAmbientPair_rightSlots, canonicalToAmbientPair_rightSlots]
    exact congrArg (pushUnionSlots b.1.2
      (by simpa [overlapSizeOfBase, unionSize] using b.2)) hright

private theorem canonicalToAmbientPair_relabel {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (σ : Equiv.Perm (Fin N))
    (τ : Equiv.Perm (Fin (p + (q - overlapSizeOfBase b))))
    (hστ : ∀ i : Fin (p + (q - overlapSizeOfBase b)),
      σ (unionSlotEmbedding b.1.2
        (by simpa [overlapSizeOfBase, unionSize] using b.2) i) =
        unionSlotEmbedding b.1.2
          (by simpa [overlapSizeOfBase, unionSize] using b.2) (τ i))
    (C : OverlapConfiguration p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b)) :
    relabelActualPair hp hq σ (canonicalToAmbientPair hp hq b C) =
      canonicalToAmbientPair hp hq b
        (relabelOverlapConfiguration (overlapLeftBound b) (overlapRightBound b) τ C) := by
  apply actualPair_eq_of_slot_sets_eq hp hq
  · rw [leftSlots_relabelActualPair, canonicalToAmbientPair_leftSlots,
      canonicalToAmbientPair_leftSlots]
    rw [pushUnionSlots_relabel b.1.2
      (by simpa [overlapSizeOfBase, unionSize] using b.2) σ τ hστ]
    rfl
  · rw [rightSlots_relabelActualPair, canonicalToAmbientPair_rightSlots,
      canonicalToAmbientPair_rightSlots]
    rw [pushUnionSlots_relabel b.1.2
      (by simpa [overlapSizeOfBase, unionSize] using b.2) σ τ hστ]
    have hR := localRightSlots_relabel
      (overlapLeftBound b) (overlapRightBound b) τ C
    change pushUnionSlots b.1.2
        (by simpa [overlapSizeOfBase, unionSize] using b.2)
        ((localRightSlots (overlapLeftBound b) (overlapRightBound b) C).map
          τ.toEmbedding) =
      pushUnionSlots b.1.2
        (by simpa [overlapSizeOfBase, unionSize] using b.2)
          (localRightSlots (overlapLeftBound b) (overlapRightBound b)
            (relabelOverlapConfiguration (overlapLeftBound b)
              (overlapRightBound b) τ C))
    exact congrArg (pushUnionSlots b.1.2
      (by simpa [overlapSizeOfBase, unionSize] using b.2)) hR.symm

private theorem ambientPair_eq_canonicalToAmbientPair {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (z : pairUnionFiber hp hq b) :
    z.1 = canonicalToAmbientPair hp hq b
      (ambientFiberOverlapEquiv hp hq b z) := by
  let y := ambientFiberToCanonical hp hq b z
  let C := ambientFiberOverlapEquiv hp hq b z
  let e := overlapConfigurationFiberEquiv (overlapLeftBound b)
    (overlapRightBound b)
  have he : e C = y := by
    change e (e.symm y) = y
    exact e.apply_symm_apply y
  have hleftC : C.left.1 = y.1.1 := by
    calc
      _ = (e C).1.1 := by rw [overlapConfigurationFiberEquiv_leftSlots]
      _ = y.1.1 := congrArg (fun w => w.1.1) he
  have hrightC : localRightSlots (overlapLeftBound b)
      (overlapRightBound b) C = y.2.1 := by
    calc
      _ = (e C).2.1 :=
        (overlapConfigurationFiberEquiv_rightSlots
          (overlapLeftBound b) (overlapRightBound b) C).symm
      _ = y.2.1 := congrArg (fun w => w.2.1) he
  have hU : b.1.2.card = p + (q - overlapSizeOfBase b) := by
    simpa [overlapSizeOfBase, unionSize] using b.2
  have hleftPush : pushUnionSlots b.1.2 hU C.left.1 = leftSlots hp z.1 := by
    calc
      _ = pushUnionSlots b.1.2 hU y.1.1 := congrArg _ hleftC
      _ = pushUnionSlots b.1.2 hU
          (pullUnionSlots b.1.2 hU (leftSlots hp z.1)
            (pairFiber_left_subset_union hp hq b z)) :=
        congrArg _ (ambientFiberToCanonical_leftSlots hp hq b z)
      _ = leftSlots hp z.1 :=
        push_pullUnionSlots b.1.2 hU (leftSlots hp z.1)
          (pairFiber_left_subset_union hp hq b z)
  have hrightPush : pushUnionSlots b.1.2 hU
      (localRightSlots (overlapLeftBound b) (overlapRightBound b) C) =
        rightSlots hq z.1 := by
    calc
      _ = pushUnionSlots b.1.2 hU y.2.1 := congrArg _ hrightC
      _ = pushUnionSlots b.1.2 hU
          (pullUnionSlots b.1.2 hU (rightSlots hq z.1)
            (pairFiber_right_subset_union hp hq b z)) :=
        congrArg _ (ambientFiberToCanonical_rightSlots hp hq b z)
      _ = rightSlots hq z.1 :=
        push_pullUnionSlots b.1.2 hU (rightSlots hq z.1)
          (pairFiber_right_subset_union hp hq b z)
  apply actualPair_eq_of_slot_sets_eq hp hq
  · rw [canonicalToAmbientPair_leftSlots]
    exact hleftPush.symm
  · rw [canonicalToAmbientPair_rightSlots]
    exact hrightPush.symm

/-- Any two pairs in a fixed ambient union/overlap fiber are related by a
permutation preserving that union. The local four-color permutation is
extended to the ambient slots, then transported through the frozen pair
placement map. -/
theorem exists_ambient_relabel_pair_eq {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (z z' : pairUnionFiber hp hq b) :
    ∃ σ : Equiv.Perm (Fin N),
      relabelActualPair hp hq σ z.1 = z'.1 ∧
        relabelPairPlacementBase σ b = b := by
  let C := ambientFiberOverlapEquiv hp hq b z
  let D := ambientFiberOverlapEquiv hp hq b z'
  obtain ⟨τ, hleft, hright⟩ := exists_relabelOverlapConfiguration_eq
    (overlapLeftBound b) (overlapRightBound b) C D
  let hU : b.1.2.card = p + (q - overlapSizeOfBase b) := by
    simpa [overlapSizeOfBase, unionSize] using b.2
  let eU : Fin (p + (q - overlapSizeOfBase b)) ↪ Fin N :=
    unionSlotEmbedding b.1.2 hU
  let eV : Fin (p + (q - overlapSizeOfBase b)) ↪ Fin N :=
    τ.toEmbedding.trans eU
  obtain ⟨σ, hστ⟩ := Equiv.Perm.exists_extending_pair
    eU eV eU.injective eV.injective
  have hστ' : ∀ i : Fin (p + (q - overlapSizeOfBase b)),
      σ (unionSlotEmbedding b.1.2 hU i) =
        unionSlotEmbedding b.1.2 hU (τ i) := by
    intro i
    simpa [eU, eV] using hστ i
  have hlocalPair : canonicalToAmbientPair hp hq b
        (relabelOverlapConfiguration (overlapLeftBound b)
          (overlapRightBound b) τ C) =
      canonicalToAmbientPair hp hq b D :=
    canonicalToAmbientPair_eq_of_slotSets_eq hp hq b _ _
      (by simpa [relabelOverlapConfiguration] using hleft)
      (by
        rw [localRightSlots_relabel]
        exact hright)
  have htransport := canonicalToAmbientPair_relabel hp hq b σ τ hστ' C
  have hpair : relabelActualPair hp hq σ z.1 = z'.1 := by
    calc
      relabelActualPair hp hq σ z.1 =
          relabelActualPair hp hq σ (canonicalToAmbientPair hp hq b C) :=
            congrArg (relabelActualPair hp hq σ) (ambientPair_eq_canonicalToAmbientPair hp hq b z)
      _ = canonicalToAmbientPair hp hq b
            (relabelOverlapConfiguration (overlapLeftBound b)
              (overlapRightBound b) τ C) := htransport
      _ = canonicalToAmbientPair hp hq b D := hlocalPair
      _ = z'.1 := (ambientPair_eq_canonicalToAmbientPair hp hq b z').symm
  have hkey : relabelPairPlacementBase σ b = b := by
    calc
      relabelPairPlacementBase σ b =
          relabelPairPlacementBase σ (pairPlacementKey hp hq z.1) :=
        congrArg (relabelPairPlacementBase σ) z.2.symm
      _ = pairPlacementKey hp hq (relabelActualPair hp hq σ z.1) :=
        (pairPlacementKey_relabelActualPair N p q hp hq σ z.1).symm
      _ = pairPlacementKey hp hq z'.1 := congrArg (pairPlacementKey hp hq) hpair
      _ = b := z'.2
  exact ⟨σ, hpair, hkey⟩

/-- In one fixed ambient union/overlap fiber, every globally compressed raw
pair term is the same by transitivity and permutation covariance. Thus the
normalized ambient fiber average is its canonical representative term. -/
theorem globallyCompressedAmbientFiberContribution_eq_rawTerm
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (z₀ : pairUnionFiber hp hq b)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    globallyCompressedAmbientFiberContribution N p q hp hq b A Bop =
      globallyCompressedRawPairTerm N p q hp hq z₀.1 A Bop := by
  have hconstant :
      (∑ z : pairUnionFiber hp hq b,
        globallyCompressedRawPairTerm N p q hp hq z.1 A Bop) =
      (Fintype.card (pairUnionFiber hp hq b) : ℂ) •
        globallyCompressedRawPairTerm N p q hp hq z₀.1 A Bop := by
    calc
      _ = ∑ _z : pairUnionFiber hp hq b,
            globallyCompressedRawPairTerm N p q hp hq z₀.1 A Bop := by
          apply Finset.sum_congr rfl
          intro z hz
          obtain ⟨σ, hσ, _hkey⟩ := exists_ambient_relabel_pair_eq hp hq b z₀ z
          calc
            globallyCompressedRawPairTerm N p q hp hq z.1 A Bop =
                globallyCompressedRawPairTerm N p q hp hq
                  (relabelActualPair hp hq σ z₀.1) A Bop := by
                    rw [← hσ]
            _ = globallyCompressedRawPairTerm N p q hp hq z₀.1 A Bop :=
              globallyCompressedRawPairTerm_conjugate N p q hp hq σ z₀.1 A Bop
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ,
          ← Nat.cast_smul_eq_nsmul ℂ]
  have hn : (Fintype.card (pairUnionFiber hp hq b) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨z₀⟩))
  unfold globallyCompressedAmbientFiberContribution globallyCompressedAmbientFiberSum
  rw [hconstant, smul_smul,
    inv_mul_cancel₀ hn, one_smul]

/-- Exact remaining canonical-prefix bridge: the globally compressed raw
representative for each local configuration must equal placement of the
N-independent averaged overlap kernel. This proposition is intentionally
not assumed or proved here; it is the sole operator-identification gap left
before the frozen grouping and radius bound can be assembled. -/
def canonicalPrefixRawTermPlacementStatement
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) : Prop :=
  ∀ C : OverlapConfiguration p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b),
    globallyCompressedRawPairTerm N p q hp hq
      (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C) A Bop =
    averagedOverlapKernelPlacement N p q (canonicalPrefixPairBase b) A Bop

#print axioms QuantumNLS.PlacementFiberCanonicalPrefix.canonicalPrefixPairBase_slots
#print axioms QuantumNLS.PlacementFiberCanonicalPrefix.exists_relabelOverlapConfiguration_eq
#print axioms QuantumNLS.PlacementFiberCanonicalPrefix.overlapFusionKernel_relabel
#print axioms QuantumNLS.PlacementFiberCanonicalPrefix.averagedOverlapKernel_eq_overlapFusionKernel
#print axioms QuantumNLS.PlacementFiberCanonicalPrefix.exists_ambient_relabel_pair_eq
#print axioms QuantumNLS.PlacementFiberCanonicalPrefix.globallyCompressedAmbientFiberContribution_eq_rawTerm

end QuantumNLS.PlacementFiberCanonicalPrefix

end


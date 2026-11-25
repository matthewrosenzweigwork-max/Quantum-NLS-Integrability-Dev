/-
QuantumNLS.PlacementFiberPrefixAlignedTransport — slot-aligned raw transport
for the canonical-prefix LOCAL-011 comparison.

The proof imports the accepted product-vector transport infrastructure from
RootOverlapCommutator and extends the frozen prefix-compression checkpoint.
-/
import QuantumNLS.PlacementFiberPrefixCompression
import QuantumNLS.RootOverlapCommutator

set_option maxHeartbeats 5000000

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberGrouping
  QuantumNLS.PlacementFiberBound QuantumNLS.PlacementFiberCanonicalPrefix
  QuantumNLS.PlacementFiberPrefixBridge QuantumNLS.PlacementFiberPrefixLift
  QuantumNLS.PlacementFiberPrefixSlotTransport
  QuantumNLS.PlacementFiberPrefixCompression QuantumNLS.RootOverlapCommutator

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixAlignedTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private def localRightSlots {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq) : Finset (Fin (p + (q - s))) :=
  C.right.1.map (overlapSlotEquiv hsp hsq).toEmbedding

/- The product-vector formula for applying the first-block placement. -/
omit [CompleteSpace H] in
private theorem firstPlacement_ptC {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p)
    (a : Fin p → H) (b : Fin q → H) :
    firstPlacement (q := q) A (ptC (Fin.append a b)) =
      (splitIsometry p q).symm
        (htmul (extendSymKernel A (ptC a)) (ptC b)) := by
  unfold firstPlacement
  simp only [ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [splitIsometry_ptprod_append, htmap_htmul, ContinuousLinearMap.id_apply]

/-- Reassociation of the three completed tensor blocks, proved on dense
product vectors and then extended by continuity. -/
private theorem split_assoc_ptC {k m t : ℕ}
    (x : HilbertTensorPower ℂ H k) (b : Fin m → H) (c : Fin t → H) :
    (cIso (Nat.add_assoc k m t)
      ((splitIsometry (k + m) t).symm
        (htmul ((splitIsometry k m).symm (htmul x (ptC b))) (ptC c))) :
          HilbertTensorPower ℂ H (k + (m + t))) =
      (splitIsometry k (m + t)).symm
        (htmul x (ptC (Fin.append b c))) := by
  let F : HilbertTensorPower ℂ H k →L[ℂ]
      HilbertTensorPower ℂ H (k + (m + t)) :=
    (cIso (Nat.add_assoc k m t)).toLinearIsometry.toContinuousLinearMap.comp
      ((splitIsometry (k + m) t).symm.toLinearIsometry.toContinuousLinearMap.comp
        ((htL (ptC c)).comp
          ((splitIsometry k m).symm.toLinearIsometry.toContinuousLinearMap.comp
            (htL (ptC b)))))
  let G : HilbertTensorPower ℂ H k →L[ℂ]
      HilbertTensorPower ℂ H (k + (m + t)) :=
    (splitIsometry k (m + t)).symm.toLinearIsometry.toContinuousLinearMap.comp
      (htL (ptC (Fin.append b c)))
  have hFG := eq_of_eq_on_ptC F G (fun a => by
    simp only [F, G, ContinuousLinearMap.comp_apply, htL_apply,
      LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometry.coe_toContinuousLinearMap]
    rw [split_symm_ptC, split_symm_ptC, split_symm_ptC, cIso_ptC]
    congr 1
    have hidx :
        (fun i : Fin (k + (m + t)) =>
          (Fin.append (Fin.append a b) c) (Fin.cast (Nat.add_assoc k m t).symm i)) =
          Fin.append a (Fin.append b c) := by
      funext i
      refine Fin.addCases (fun j : Fin k => ?_) (fun j : Fin (m + t) => ?_) i
      · have hi : Fin.cast (Nat.add_assoc k m t).symm (Fin.castAdd (m + t) j) =
            Fin.castAdd t (Fin.castAdd m j) := by
          apply Fin.ext
          simp
        rw [hi]
        simp [Fin.append]
      · refine Fin.addCases (fun j : Fin m => ?_) (fun j : Fin t => ?_) j
        · have hi : Fin.cast (Nat.add_assoc k m t).symm
              (Fin.natAdd k (Fin.castAdd t j)) = Fin.castAdd t (Fin.natAdd k j) := by
            apply Fin.ext
            simp
          rw [hi]
          simp [Fin.append]
        · have hi : Fin.cast (Nat.add_assoc k m t).symm
              (Fin.natAdd k (Fin.natAdd m j)) = Fin.natAdd (k + m) j := by
            apply Fin.ext
            simp
            omega
          rw [hi]
          simp [Fin.append]
    exact hidx)
  have h := congrArg (fun T : HilbertTensorPower ℂ H k →L[ℂ]
      HilbertTensorPower ℂ H (k + (m + t)) => T x) hFG
  simpa [F, G, ContinuousLinearMap.comp_apply, htL_apply, htR_apply] using h

/-- Prefix-lifting the first-block placement is the first-block placement
after the three tensor blocks have been reassociated. -/
private theorem prefixTensorLift_firstPlacement {k m t : ℕ}
    (A : SymSector ℂ H k →L[ℂ] SymSector ℂ H k) :
    castTensorOperator (Nat.add_assoc k m t)
      (prefixTensorLift (H := H) (r := k + m) (t := t)
        (firstPlacement (q := m) A)) = firstPlacement (q := m + t) A := by
  apply eq_of_eq_on_ptC
  intro f
  let a : Fin k → H := fun i => f (Fin.castAdd (m + t) i)
  let b : Fin m → H := fun i => f (Fin.natAdd k (Fin.castAdd t i))
  let c : Fin t → H := fun i => f (Fin.natAdd k (Fin.natAdd m i))
  have hf : f = Fin.append a (Fin.append b c) := by
    exact eq_append3 f
  rw [hf, castTensorOperator_eq_conj, cIso_symm_ptC]
  have hcast :
      (fun i : Fin ((k + m) + t) =>
        (Fin.append a (Fin.append b c)) (Fin.cast (Nat.add_assoc k m t) i)) =
        Fin.append (Fin.append a b) c := by
    funext i
    refine Fin.addCases (fun j : Fin (k + m) => ?_) (fun j : Fin t => ?_) i
    · refine Fin.addCases (fun j : Fin k => ?_) (fun j : Fin m => ?_) j
      · have hi : Fin.cast (Nat.add_assoc k m t) (Fin.castAdd t (Fin.castAdd m j)) =
            Fin.castAdd (m + t) j := by
          apply Fin.ext
          simp
        rw [hi]
        simp [Fin.append]
      · have hi : Fin.cast (Nat.add_assoc k m t)
              (Fin.castAdd t (Fin.natAdd k j)) = Fin.natAdd k (Fin.castAdd t j) := by
          apply Fin.ext
          simp
        rw [hi]
        simp [Fin.append]
    · have hi : Fin.cast (Nat.add_assoc k m t) (Fin.natAdd (k + m) j) =
          Fin.natAdd k (Fin.natAdd m j) := by
        apply Fin.ext
        simp
        omega
      rw [hi]
      simp [Fin.append]
  rw [show (ptC (fun i : Fin ((k + m) + t) =>
      (Fin.append a (Fin.append b c)) (Fin.cast (Nat.add_assoc k m t) i)) :
      HilbertTensorPower ℂ H ((k + m) + t)) = ptC (Fin.append (Fin.append a b) c) by
        rw [hcast]]
  unfold prefixTensorLift
  simp only [ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [splitIsometry_ptprod_append, htmap_htmul, ContinuousLinearMap.id_apply,
    firstPlacement_ptC, firstPlacement_ptC]
  exact split_assoc_ptC (extendSymKernel A (ptC a)) b c

/-- The subset placement induced on a longer prefix by a local placement. -/
private def prefixPlacementSubset {k m t : ℕ}
    (S : PlacementSubset k m) : PlacementSubset k (m + t) := by
  refine ⟨S.1.map (Fin.castLEEmb (by omega)), ?_⟩
  rw [Finset.card_map]
  exact S.2

omit [CompleteSpace H] in
private theorem castTensorOperator_comp {m n : ℕ} (h : m = n)
    (X Y : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) :
    castTensorOperator h (X.comp Y) =
      (castTensorOperator h X).comp (castTensorOperator h Y) := by
  cases h
  rfl

omit [CompleteSpace H] in
private theorem castTensorOperator_permRep {m n : ℕ} (h : m = n)
    (σ : Equiv.Perm (Fin m)) :
    castTensorOperator h (permRep ℂ H m σ :
      HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) =
      (permRep ℂ H n (castPermBack h.symm σ) :
        HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) := by
  cases h
  rfl

private theorem castPermBack_apply {m n : ℕ} (h : m = n)
    (σ : Equiv.Perm (Fin n)) (i : Fin m) :
    castPermBack h σ i = Fin.cast h.symm (σ (Fin.cast h i)) := by
  cases h
  rfl

omit [CompleteSpace H] in
private theorem permRep_inv_clm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permRep ℂ H n σ⁻¹ :
      HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) =
      (↑((permRep ℂ H n σ)⁻¹) :
        HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) := by
  exact congrArg (fun U : unitary
      (HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) =>
        (U : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n))
    (map_inv (permRep ℂ H n) σ)

private theorem castBlockPerm_prefix {k m t : ℕ}
    (h : (k + m) + t = k + (m + t))
    (τ : Equiv.Perm (Fin (k + m))) (i : Fin k) :
    castPermBack h.symm (blockPerm τ (1 : Equiv.Perm (Fin t)))
        (Fin.castAdd (m + t) i) =
      Fin.castLE (by omega) (τ (Fin.castAdd m i)) := by
  have hcast :
      Fin.cast h.symm (Fin.castAdd (m + t) i) =
        Fin.castAdd t (Fin.castAdd m i) := by
    apply Fin.ext
    simp
  have hback (j : Fin (k + m)) :
      Fin.cast h (Fin.castAdd t j) = Fin.castLE (by omega) j := by
    apply Fin.ext
    simp
  rw [castPermBack_apply]
  rw [hcast, blockPerm_castAdd]
  exact hback _

private def conjugateTensorOperator {n : ℕ} (σ : Equiv.Perm (Fin n))
    (T : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) :
    HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n :=
  ((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ]
      HilbertTensorPower ℂ H n).comp T).comp
    (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ]
      HilbertTensorPower ℂ H n)

/- The proof only needs the Hilbert tensor structure, not completeness. -/
omit [CompleteSpace H] in
private theorem prefixTensorLift_permutedPlacement {k m t : ℕ}
    (τ : Equiv.Perm (Fin (k + m)))
    (A : SymSector ℂ H k →L[ℂ] SymSector ℂ H k) :
    prefixTensorLift (H := H) (r := k + m) (t := t)
        (permutedPlacement τ A) =
      conjugateTensorOperator (blockPerm τ (1 : Equiv.Perm (Fin t)))
        (prefixTensorLift (H := H) (r := k + m) (t := t)
          (firstPlacement (q := m) A)) := by
  unfold permutedPlacement conjugateTensorOperator
  rw [← prefixTensorLift_comp, ← prefixTensorLift_comp]
  rw [prefixTensorLift_permRep, prefixTensorLift_permRep]
  have hinv : blockPerm τ⁻¹ (1 : Equiv.Perm (Fin t)) =
      (blockPerm τ (1 : Equiv.Perm (Fin t)))⁻¹ := by
    exact (blockPerm_symm τ (1 : Equiv.Perm (Fin t))).symm
  rw [hinv]

/-- Prefix lifting a local subset placement gives the corresponding placement
on the longer tensor power, with the same ordered kernel action. -/
private theorem prefixTensorLift_subsetPlacement {k m t : ℕ}
    (S : PlacementSubset k m)
    (A : SymSector ℂ H k →L[ℂ] SymSector ℂ H k) :
    castTensorOperator (Nat.add_assoc k m t)
      (prefixTensorLift (H := H) (r := k + m) (t := t)
        (subsetPlacement S A)) =
      subsetPlacement (prefixPlacementSubset (t := t) S) A := by
  let τ := subsetRepresentative S
  have hrep : placementSubsetOfPerm τ = S := subsetRepresentative_maps S
  have hlocal : subsetPlacement S A = permutedPlacement τ A :=
    (permutedPlacement_eq_subsetPlacement τ S hrep A).symm
  let ρ := blockPerm τ (1 : Equiv.Perm (Fin t))
  let σ := castPermBack (Nat.add_assoc k m t).symm ρ
  rw [hlocal, prefixTensorLift_permutedPlacement]
  have hbase := prefixTensorLift_firstPlacement (H := H) (k := k) (m := m) (t := t) A
  calc
    castTensorOperator (Nat.add_assoc k m t)
        (conjugateTensorOperator ρ
          (prefixTensorLift (H := H) (r := k + m) (t := t)
            (firstPlacement (q := m) A))) =
      permutedPlacement σ A := by
      unfold conjugateTensorOperator
      rw [castTensorOperator_comp, castTensorOperator_comp,
        castTensorOperator_permRep, hbase, castTensorOperator_permRep]
      simp [σ, castPermBack_inv]
      unfold permutedPlacement
      rw [permRep_inv_clm]
    _ = subsetPlacement (prefixPlacementSubset (t := t) S) A := by
      have himage : placementSubsetOfPerm σ = prefixPlacementSubset (t := t) S := by
        apply Subtype.ext
        change (firstPositions (p := k) (q := m + t)).map σ.toEmbedding =
          S.1.map (Fin.castLEEmb (show k + m ≤ k + (m + t) by omega))
        have hrepSet : S.1 =
            (firstPositions (p := k) (q := m)).map τ.toEmbedding := by
          exact (congrArg Subtype.val hrep).symm
        rw [hrepSet]
        unfold firstPositions
        rw [Finset.map_map, Finset.map_map]
        ext x
        simp only [Finset.mem_map, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, rfl⟩
          refine ⟨Fin.castAdd m i, ⟨i, rfl⟩, ?_⟩
          calc
            ((τ.toEmbedding).trans
                (Fin.castLEEmb (show k + m ≤ k + (m + t) by omega)))
                (Fin.castAdd m i) = Fin.castLE (by omega)
                  (τ (Fin.castAdd m i)) := rfl
            _ = σ (Fin.castAdd (m + t) i) :=
              (castBlockPerm_prefix (Nat.add_assoc k m t) τ i).symm
        · rintro ⟨i, hi, hix⟩
          obtain ⟨j, hji⟩ := hi
          subst i
          refine ⟨j, ?_⟩
          change σ (Fin.castAdd (m + t) j) = x
          calc
            σ (Fin.castAdd (m + t) j) = Fin.castLE (by omega)
                (τ (Fin.castAdd m j)) :=
              castBlockPerm_prefix (Nat.add_assoc k m t) τ j
            _ = ((τ.toEmbedding).trans
                (Fin.castLEEmb (show k + m ≤ k + (m + t) by omega)))
                (Fin.castAdd m j) := rfl
            _ = x := hix
      exact permutedPlacement_eq_subsetPlacement σ _ himage A

omit [CompleteSpace H] in
private theorem castSubsetPlacement_sourceSlots {N p q : ℕ}
    (h : p + q = N) (hp : p ≤ N)
    (S : PlacementSubset p q) (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    castTensorOperator h (subsetPlacement S A) =
      castTensorOperator (Nat.add_sub_of_le hp)
        (subsetPlacement
          (sourcePlacementOfSlots hp (castSlotSet h S.1)
            (by simpa [castSlotSet] using S.2)) A) := by
  have hq : q = N - p := by omega
  subst q
  have hh : h = Nat.add_sub_of_le hp := Subsingleton.elim _ _
  have hS : sourcePlacementOfSlots hp (castSlotSet h S.1)
      (by simpa [castSlotSet] using S.2) = S := by
    apply Subtype.ext
    change castSlotSet (Nat.add_sub_of_le hp).symm
      (castSlotSet h S.1) = S.1
    rw [hh]
    exact castSlotSet_symm _ _
  rw [hS, hh]

omit [CompleteSpace H] in
private theorem castSubsetPlacement_eq_of_slots {N p q m : ℕ}
    (h₁ : p + q = N) (h₂ : p + m = N) (hp : p ≤ N)
    (S : PlacementSubset p q) (T : PlacementSubset p m)
    (hslots : castSlotSet h₁ S.1 = castSlotSet h₂ T.1)
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    castTensorOperator h₁ (subsetPlacement S A) =
      castTensorOperator h₂ (subsetPlacement T A) := by
  rw [castSubsetPlacement_sourceSlots h₁ hp S A,
    castSubsetPlacement_sourceSlots h₂ hp T A]
  have hsource :
      sourcePlacementOfSlots hp (castSlotSet h₁ S.1)
          (by simpa [castSlotSet] using S.2) =
        sourcePlacementOfSlots hp (castSlotSet h₂ T.1)
          (by simpa [castSlotSet] using T.2) := by
    apply Subtype.ext
    change castSlotSet (Nat.add_sub_of_le hp).symm
        (castSlotSet h₁ S.1) =
      castSlotSet (Nat.add_sub_of_le hp).symm (castSlotSet h₂ T.1)
    exact congrArg (castSlotSet (Nat.add_sub_of_le hp).symm) hslots
  rw [hsource]

private theorem finset_map_eq_of_pointwise {α β : Type*}
    (S : Finset α) (e f : α ↪ β) (h : ∀ a, e a = f a) :
    S.map e = S.map f := by
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, ha, (h a).symm.trans hax⟩
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, ha, (h a).trans hax⟩

private theorem cast_prefixPlacementSubset_slots {k m t N : ℕ}
    (h : k + (m + t) = N) (hkm : k + m ≤ N)
    (S : PlacementSubset k m) :
    castSlotSet h (prefixPlacementSubset (t := t) S).1 =
      S.1.map (Fin.castLEEmb hkm) := by
  cases h
  unfold castSlotSet prefixPlacementSubset
  rw [Finset.map_map]
  apply finset_map_eq_of_pointwise
  intro i
  apply Fin.ext
  simp

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
private theorem prefixTensorLift_cast {r r' t : ℕ} (h : r = r')
    (T : HilbertTensorPower ℂ H r →L[ℂ] HilbertTensorPower ℂ H r) :
    castTensorOperator (congrArg (fun n : ℕ => n + t) h)
        (prefixTensorLift (H := H) (r := r) (t := t) T) =
      prefixTensorLift (H := H) (r := r') (t := t)
        (castTensorOperator h T) := by
  cases h
  rfl

private theorem localRightSlots_prefixSupport {p q s N : ℕ}
    {hsp : s ≤ p} {hsq : s ≤ q}
    (hr : p + (q - s) ≤ N)
    (C : OverlapConfiguration p q s hsp hsq) :
    (localRightSlots hsp hsq C).map (Fin.castLEEmb hr) =
      C.right.1.map (Fin.castLEEmb (by omega)) := by
  unfold localRightSlots overlapSlotEquiv
  rw [Finset.map_map]
  apply finset_map_eq_of_pointwise
  intro i
  apply Fin.ext
  let hdim := canonicalRightDimensionEq p q s hsp hsq
  change (Fin.castLE hr (Equiv.cast (congrArg Fin hdim) i)).val =
    (Fin.castLE (by omega) i).val
  rw [RootOverlapCommutator.equivCast_eq_finCast hdim i]
  rfl

/-- The slot-aligned canonical pair transports its two raw factors to the
prefix lifts of the local ordered factors.  The final composition therefore
has exactly the ordered operator stated in LOCAL-011. -/
theorem canonicalPrefixAlignedRawOperatorTransport
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    canonicalPrefixAlignedRawOperatorTransportGap hp hq b A Bop := by
  intro C σ hleft hright
  let b₀ := canonicalPrefixPairBase b
  let s := overlapSizeOfBase b₀
  let r := p + (q - s)
  let t := N - r
  have hsp : s ≤ p := overlapLeftBound b₀
  have hsq : s ≤ q := overlapRightBound b₀
  have hr : r ≤ N := pairPlacementBase_unionSize_le_N b₀
  have hN : r + t = N := Nat.add_sub_of_le hr
  let z := relabelActualPair hp hq σ
    (canonicalToAmbientPair hp hq b₀ C)
  change leftSlots hp z = C.left.1.map (Fin.castLEEmb hr) at hleft
  change rightSlots hq z =
    (localRightSlots hsp hsq C).map (Fin.castLEEmb hr) at hright
  let prefLeft := prefixPlacementSubset (t := t) C.left
  let prefRight := prefixPlacementSubset (t := t) C.right
  have hNleft : p + ((q - s) + t) = N := by
    dsimp [r, t] at hN hr ⊢
    omega
  have hNright : q + ((p - s) + t) = N := by
    dsimp [r, t] at hN hr ⊢
    omega
  have hRtail : q + (p - s) ≤ N := by
    rw [canonicalRightDimensionEq p q s hsp hsq]
    exact hr
  have hleftSlots :
      castSlotSet (Nat.add_sub_of_le hp) z.1.1 =
        castSlotSet hNleft prefLeft.1 := by
    calc
      _ = leftSlots hp z := rfl
      _ = C.left.1.map (Fin.castLEEmb hr) := hleft
      _ = castSlotSet hNleft prefLeft.1 :=
        (cast_prefixPlacementSubset_slots hNleft hr C.left).symm
  have hrightSlots :
      castSlotSet (Nat.add_sub_of_le hq) z.2.1 =
        castSlotSet hNright prefRight.1 := by
    calc
      _ = rightSlots hq z := rfl
      _ = (localRightSlots hsp hsq C).map (Fin.castLEEmb hr) := hright
      _ = C.right.1.map (Fin.castLEEmb hRtail) :=
        localRightSlots_prefixSupport hr C
      _ = castSlotSet hNright prefRight.1 :=
        (cast_prefixPlacementSubset_slots hNright hRtail C.right).symm
  have hleftOp := castSubsetPlacement_eq_of_slots
    (Nat.add_sub_of_le hp) hNleft hp z.1 prefLeft hleftSlots A
  have hrightOp := castSubsetPlacement_eq_of_slots
    (Nat.add_sub_of_le hq) hNright hq z.2 prefRight hrightSlots Bop
  have hprefixLeft := prefixTensorLift_subsetPlacement
    (k := p) (m := q - s) (t := t) C.left A
  have hprefixRight := prefixTensorLift_subsetPlacement
    (k := q) (m := p - s) (t := t) C.right Bop
  have hleftCast : (Nat.add_assoc p (q - s) t).trans hNleft =
      Nat.add_sub_of_le hr := Subsingleton.elim _ _
  have hleftFactor :
      castTensorOperator (Nat.add_sub_of_le hp) (subsetPlacement z.1 A) =
        castTensorOperator (Nat.add_sub_of_le hr)
          (prefixTensorLift (H := H) (r := r) (t := t)
            (subsetPlacement C.left A)) := by
    calc
      _ = castTensorOperator hNleft (subsetPlacement prefLeft A) := hleftOp
      _ = castTensorOperator hNleft
          (castTensorOperator (Nat.add_assoc p (q - s) t)
            (prefixTensorLift (H := H) (r := r) (t := t)
              (subsetPlacement C.left A))) :=
        congrArg (castTensorOperator hNleft) hprefixLeft.symm
      _ = castTensorOperator ((Nat.add_assoc p (q - s) t).trans hNleft)
          (prefixTensorLift (H := H) (r := r) (t := t)
            (subsetPlacement C.left A)) :=
        castTensorOperator_trans _ _ _
      _ = _ := by rw [hleftCast]
  have hrightCast : (Nat.add_assoc q (p - s) t).trans hNright =
      (congrArg (fun n : ℕ => n + t)
        (canonicalRightDimensionEq p q s hsp hsq)).trans
        (Nat.add_sub_of_le hr) := Subsingleton.elim _ _
  have hrightDim := canonicalRightDimensionEq p q s hsp hsq
  have hrightDef : rightPlacement C Bop =
      castTensorOperator hrightDim (subsetPlacement C.right Bop) := by
    unfold rightPlacement
    congr 1
  have hrightLiftCast := prefixTensorLift_cast (t := t) hrightDim
    (subsetPlacement C.right Bop)
  have hrightFactor :
      castTensorOperator (Nat.add_sub_of_le hq) (subsetPlacement z.2 Bop) =
        castTensorOperator (Nat.add_sub_of_le hr)
          (prefixTensorLift (H := H) (r := r) (t := t)
            (rightPlacement C Bop)) := by
    calc
      _ = castTensorOperator hNright (subsetPlacement prefRight Bop) := hrightOp
      _ = castTensorOperator hNright
          (castTensorOperator (Nat.add_assoc q (p - s) t)
            (prefixTensorLift (H := H) (r := q + (p - s)) (t := t)
              (subsetPlacement C.right Bop))) :=
        congrArg (castTensorOperator hNright) hprefixRight.symm
      _ = castTensorOperator ((Nat.add_assoc q (p - s) t).trans hNright)
          (prefixTensorLift (H := H) (r := q + (p - s)) (t := t)
            (subsetPlacement C.right Bop)) :=
        castTensorOperator_trans _ _ _
      _ = castTensorOperator
          ((congrArg (fun n : ℕ => n + t) hrightDim).trans
            (Nat.add_sub_of_le hr))
          (prefixTensorLift (H := H) (r := q + (p - s)) (t := t)
            (subsetPlacement C.right Bop)) := by rw [hrightCast]
      _ = castTensorOperator (Nat.add_sub_of_le hr)
          (castTensorOperator (congrArg (fun n : ℕ => n + t) hrightDim)
            (prefixTensorLift (H := H) (r := q + (p - s)) (t := t)
              (subsetPlacement C.right Bop))) :=
        (castTensorOperator_trans _ _ _).symm
      _ = castTensorOperator (Nat.add_sub_of_le hr)
          (prefixTensorLift (H := H) (r := r) (t := t)
            (castTensorOperator hrightDim (subsetPlacement C.right Bop))) :=
        congrArg (castTensorOperator (Nat.add_sub_of_le hr)) hrightLiftCast
      _ = castTensorOperator (Nat.add_sub_of_le hr)
          (prefixTensorLift (H := H) (r := r) (t := t)
            (rightPlacement C Bop)) := by rw [← hrightDef]
  change (castTensorOperator (Nat.add_sub_of_le hp) (subsetPlacement z.1 A)).comp
      (castTensorOperator (Nat.add_sub_of_le hq) (subsetPlacement z.2 Bop)) =
    castTensorOperator (Nat.add_sub_of_le hr)
      (prefixTensorLift (H := H) (r := r) (t := t)
        ((subsetPlacement C.left A).comp (rightPlacement C Bop)))
  rw [hleftFactor, hrightFactor, ← castTensorOperator_comp,
    prefixTensorLift_comp]

/-- The frozen compression reduction closes once both ordered raw factors
are transported to the aligned prefix slots. -/
theorem globallyCompressedCanonicalPrefixRawPairTerm_eq_averagedPlacement
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    canonicalPrefixRawTermPlacementStatement hp hq b A Bop :=
  globallyCompressedCanonicalPrefixRawPairTerm_eq_averagedPlacement_of_alignedTransport
    hp hq b A Bop (canonicalPrefixAlignedRawOperatorTransport hp hq b A Bop)

/-- The now-closed raw-term identity identifies each normalized ambient
union/overlap fiber with placement of the N-independent averaged kernel. -/
theorem globallyCompressedAmbientFiberContribution_eq_averagedOverlapKernelPlacement
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    globallyCompressedAmbientFiberContribution N p q hp hq b A Bop =
      averagedOverlapKernelPlacement N p q b A Bop := by
  apply (fiberOperatorIdentity_iff_canonicalPrefix hp hq b A Bop).mpr
  let b₀ := canonicalPrefixPairBase b
  let s := overlapSizeOfBase b₀
  let hsp := overlapLeftBound b₀
  let hsq := overlapRightBound b₀
  have hcard : 0 < Fintype.card (OverlapConfiguration p q s hsp hsq) := by
    rw [card_overlapConfiguration hsp hsq]
    apply Nat.mul_pos
    · exact Nat.choose_pos (by dsimp [s, overlapSizeOfBase, unionSize]; omega)
    · exact Nat.choose_pos hsp
  let C : OverlapConfiguration p q s hsp hsq :=
    Classical.choice (Fintype.card_pos_iff.mp hcard)
  let z₀ : pairUnionFiber hp hq b₀ :=
    canonicalToAmbientFiber hp hq b₀ C
  have hraw : z₀.1 = canonicalToAmbientPair hp hq b₀ C := by
    rfl
  calc
    globallyCompressedAmbientFiberContribution N p q hp hq b₀ A Bop =
        globallyCompressedRawPairTerm N p q hp hq z₀.1 A Bop :=
      globallyCompressedAmbientFiberContribution_eq_rawTerm hp hq b₀ z₀ A Bop
    _ = averagedOverlapKernelPlacement N p q b₀ A Bop := by
      rw [hraw]
      exact globallyCompressedCanonicalPrefixRawPairTerm_eq_averagedPlacement
        hp hq b A Bop C

abbrev FeasibleOverlapIndex (N p q : ℕ) :=
  {s : Fin (min p q + 1) // unionSize p q s.1 ≤ N}

abbrev AmbientUnionSlots (N p q s : ℕ) :=
  {U : Finset (Fin N) // U.card = unionSize p q s}

def pairBaseOfOverlapUnion {N p q : ℕ}
    (s : FeasibleOverlapIndex N p q) (U : AmbientUnionSlots N p q s.1.1) :
    PairPlacementBase N p q :=
  ⟨(⟨s.1.1, Nat.lt_succ_iff.mp s.1.2⟩, U.1), U.2⟩

/-- Reindexing a pair base exposes its feasible overlap and its actual
ambient union subset as independent finite indices. -/
noncomputable def pairPlacementBaseOverlapUnionEquiv (N p q : ℕ) :
    PairPlacementBase N p q ≃
      Σ s : FeasibleOverlapIndex N p q, AmbientUnionSlots N p q s.1.1 := by
  classical
  refine
    { toFun := fun b =>
        ⟨⟨⟨b.1.1.1, Nat.lt_succ_of_le b.1.1.2⟩,
          pairPlacementBase_unionSize_le_N b⟩,
          ⟨b.1.2, b.2⟩⟩
      invFun := fun y => pairBaseOfOverlapUnion y.1 y.2
      left_inv := ?_
      right_inv := ?_ }
  · intro b
    apply Subtype.ext
    rfl
  · intro y
    cases y with
    | mk s U =>
      rcases s with ⟨s, hs⟩
      rcases U with ⟨U, hU⟩
      rfl

/-- Ambient union subsets and source placement subsets are the same finite
index set after the proved slot cast. -/
noncomputable def ambientUnionSlotsPlacementEquiv {N r : ℕ} (hr : r ≤ N) :
    {U : Finset (Fin N) // U.card = r} ≃ PlacementSubset r (N - r) where
  toFun U := sourcePlacementOfSlots hr U.1 U.2
  invFun S :=
    ⟨castSlotSet (Nat.add_sub_of_le hr) S.1, by simp [castSlotSet, S.2]⟩
  left_inv U := by
    apply Subtype.ext
    exact slots_sourcePlacementOfSlots hr U.1 U.2
  right_inv S := by
    apply Subtype.ext
    change castSlotSet (Nat.add_sub_of_le hr).symm
      (castSlotSet (Nat.add_sub_of_le hr) S.1) = S.1
    exact castSlotSet_symm (Nat.add_sub_of_le hr) S.1

private theorem ambientUnionSlots_average_eq_genericU
    {N r : ℕ} (hr : r ≤ N) (K : BoundedSymmetricKernel H r) :
    ((Nat.choose N r : ℂ)⁻¹) •
        ∑ U : {U : Finset (Fin N) // U.card = r},
          arbitraryNSectorSubsetPlacement N r hr
            (sourcePlacementOfSlots hr U.1 U.2) K =
      genericU_N_r N r hr K := by
  classical
  let E := ambientUnionSlotsPlacementEquiv hr
  have hsum :
      (∑ U : {U : Finset (Fin N) // U.card = r},
        arbitraryNSectorSubsetPlacement N r hr
          (sourcePlacementOfSlots hr U.1 U.2) K) =
        ∑ S : PlacementSubset r (N - r),
          arbitraryNSectorSubsetPlacement N r hr S K := by
    exact Equiv.sum_comp E
      (fun S => arbitraryNSectorSubsetPlacement N r hr S K)
  rw [hsum, genericU_N_r_eq_arbitraryNSectorSubsetAverage]
  rfl

private theorem sourceNormalizedAmbientFiberTerm_eq_averagePlacement
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    sourceNormalizedAmbientFiberTerm N p q hp hq b A Bop =
      ((((overlapCoefficient N p q (overlapSizeOfBase b) : ℝ) : ℂ) *
          (Nat.choose N (unionSize p q (overlapSizeOfBase b)) : ℂ)⁻¹) •
        averagedOverlapKernelPlacement N p q b A Bop) := by
  rw [sourceNormalizedAmbientFiberTerm,
    globallyCompressedAmbientFiberContribution_eq_averagedOverlapKernelPlacement
      hp hq b A Bop]

/-- The N-independent finite-degree product expansion. Only feasible union
sizes are indexed; the omitted overlap sizes have zero source coefficient. -/
theorem genericU_product_eq_overlapKernelExpansion
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (genericU_N_r N p hp A).comp (genericU_N_r N q hq Bop) =
      ∑ s : FeasibleOverlapIndex N p q,
        (((overlapCoefficient N p q s.1.1 : ℝ) : ℂ) •
          genericU_N_r N (unionSize p q s.1.1) s.2
            (averagedOverlapKernel
              (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
              (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)) A Bop)) := by
  classical
  rw [genericU_product_eq_sourceNormalizedAmbientFiberGrouping]
  let E := pairPlacementBaseOverlapUnionEquiv N p q
  have hindex :
      (∑ b : PairPlacementBase N p q,
        sourceNormalizedAmbientFiberTerm N p q hp hq b A Bop) =
        ∑ y : Σ s : FeasibleOverlapIndex N p q,
            AmbientUnionSlots N p q s.1.1,
          sourceNormalizedAmbientFiberTerm N p q hp hq (E.symm y) A Bop := by
    exact Equiv.sum_comp E
      (fun y => sourceNormalizedAmbientFiberTerm N p q hp hq (E.symm y) A Bop)
  rw [hindex, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  let r := unionSize p q s.1.1
  let hr := s.2
  let K := averagedOverlapKernel
    (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
    (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)) A Bop
  have hinner :
      (∑ U : AmbientUnionSlots N p q s.1.1,
        sourceNormalizedAmbientFiberTerm N p q hp hq
          (pairBaseOfOverlapUnion s U) A Bop) =
        (((overlapCoefficient N p q s.1.1 : ℝ) : ℂ) •
          genericU_N_r N r hr K) := by
    have hterms (U : AmbientUnionSlots N p q s.1.1) :
        sourceNormalizedAmbientFiberTerm N p q hp hq
            (pairBaseOfOverlapUnion s U) A Bop =
        ((((overlapCoefficient N p q s.1.1 : ℝ) : ℂ) *
              (Nat.choose N r : ℂ)⁻¹) •
            arbitraryNSectorSubsetPlacement N r hr
              (sourcePlacementOfSlots hr U.1 U.2) K) := by
      rw [sourceNormalizedAmbientFiberTerm_eq_averagePlacement]
      simp [pairBaseOfOverlapUnion, r, K, averagedOverlapKernelPlacement,
        overlapSizeOfBase, unionSize]
    calc
      _ = ∑ U : AmbientUnionSlots N p q s.1.1,
            ((((overlapCoefficient N p q s.1.1 : ℝ) : ℂ) *
                (Nat.choose N r : ℂ)⁻¹) •
              arbitraryNSectorSubsetPlacement N r hr
                (sourcePlacementOfSlots hr U.1 U.2) K) := by
          apply Finset.sum_congr rfl
          intro U hU
          exact hterms U
      _ = (((overlapCoefficient N p q s.1.1 : ℝ) : ℂ) *
              (Nat.choose N r : ℂ)⁻¹) •
            ∑ U : AmbientUnionSlots N p q s.1.1,
              arbitraryNSectorSubsetPlacement N r hr
                (sourcePlacementOfSlots hr U.1 U.2) K := by
          rw [Finset.smul_sum]
      _ = (((overlapCoefficient N p q s.1.1 : ℝ) : ℂ) •
            genericU_N_r N r hr K) := by
          rw [← smul_smul]
          apply congrArg (fun x : SymSector ℂ H N →L[ℂ] SymSector ℂ H N =>
            ((overlapCoefficient N p q s.1.1 : ℝ) : ℂ) • x)
          simpa [r] using ambientUnionSlots_average_eq_genericU hr K
  simpa [E, pairPlacementBaseOverlapUnionEquiv, r, hr, K,
    pairBaseOfOverlapUnion] using hinner

def feasibleOverlapFinset (N p q : ℕ) : Finset ℕ :=
  (Finset.range (min p q + 1)).filter (fun s => unionSize p q s ≤ N)

noncomputable def feasibleOverlapFilterEquiv (N p q : ℕ) :
    FeasibleOverlapIndex N p q ≃
      {s : ℕ // s ∈ feasibleOverlapFinset N p q} where
  toFun s :=
    ⟨s.1.1, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr s.1.2, s.2⟩⟩
  invFun s :=
    ⟨⟨s.1, Finset.mem_range.mp (Finset.mem_filter.mp s.2).1⟩,
      (Finset.mem_filter.mp s.2).2⟩
  left_inv s := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl

def feasibleOverlapRadiusTerm (N p q : ℕ) (R : ℝ)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q)
    (s : FeasibleOverlapIndex N p q) : ℝ :=
  overlapCoefficient N p q s.1.1 *
    (R ^ unionSize p q s.1.1 *
      ‖averagedOverlapKernel
        (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
        (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)) A Bop‖)

private theorem feasibleOverlapRadius_sum_le
    {N p q : ℕ} {R : ℝ} (hp : p ≤ N) (hq : q ≤ N) (hR : 1 ≤ R)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (∑ s : FeasibleOverlapIndex N p q,
      feasibleOverlapRadiusTerm N p q R A Bop s) ≤
      (R ^ p * ‖A‖) * (R ^ q * ‖Bop‖) := by
  classical
  let S := Finset.range (min p q + 1)
  let F := feasibleOverlapFinset N p q
  let E := feasibleOverlapFilterEquiv N p q
  have hindex :
      (∑ s : FeasibleOverlapIndex N p q,
        feasibleOverlapRadiusTerm N p q R A Bop s) =
        ∑ s ∈ F, sourceWeightedOverlapTerm N p q R A Bop s := by
    calc
      _ = ∑ s : FeasibleOverlapIndex N p q,
            sourceWeightedOverlapTerm N p q R A Bop s.1.1 := by
          apply Finset.sum_congr rfl
          intro s hs
          have hmin : s.1.1 ≤ min p q := Nat.le_of_lt_succ s.1.2
          simp [feasibleOverlapRadiusTerm, sourceWeightedOverlapTerm, hmin]
      _ = ∑ s : {s : ℕ // s ∈ F},
            sourceWeightedOverlapTerm N p q R A Bop s.1 := by
          calc
            _ = ∑ s : FeasibleOverlapIndex N p q,
                  sourceWeightedOverlapTerm N p q R A Bop (E s).1 := by
                apply Finset.sum_congr rfl
                intro s hs
                rfl
            _ = _ := Equiv.sum_comp E
              (fun s => sourceWeightedOverlapTerm N p q R A Bop s.1)
      _ = ∑ s ∈ F, sourceWeightedOverlapTerm N p q R A Bop s := by
          exact Finset.sum_attach F
            (fun s => sourceWeightedOverlapTerm N p q R A Bop s)
  have hfilter :
      (∑ s ∈ F, sourceWeightedOverlapTerm N p q R A Bop s) =
        ∑ s ∈ S, sourceWeightedOverlapTerm N p q R A Bop s := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro s hs hnot
    have hsmin : s ≤ min p q := by
      have hs' := Finset.mem_range.mp hs
      omega
    have hlarge : N < unionSize p q s := by
      apply Nat.lt_of_not_ge
      intro hsmall
      apply hnot
      exact Finset.mem_filter.mpr ⟨hs, hsmall⟩
    have hsQ : s ≤ q := le_trans hsmin (min_le_right _ _)
    simp [sourceWeightedOverlapTerm, hsmin,
      overlapCoefficient_eq_zero_of_unionSize_gt hp hsQ hlarge]
  rw [hindex, hfilter]
  exact sourceWeightedOverlap_radius_majorant hp hq hR A Bop

private theorem norm_feasibleOverlapExpansionTerm_le
    {N p q : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q)
    (s : FeasibleOverlapIndex N p q) :
    ‖(((overlapCoefficient N p q s.1.1 : ℝ) : ℂ) •
        genericU_N_r N (unionSize p q s.1.1) s.2
          (averagedOverlapKernel
            (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
            (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)) A Bop))‖ ≤
      feasibleOverlapRadiusTerm N p q R A Bop s := by
  let r := unionSize p q s.1.1
  let K := averagedOverlapKernel
    (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
    (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)) A Bop
  have hc : 0 ≤ overlapCoefficient N p q s.1.1 := by
    have hq : q ≤ N := by
      have hmin : s.1.1 ≤ min p q := Nat.le_of_lt_succ s.1.2
      have hr := s.2
      dsimp [unionSize] at hr
      omega
    have hden : 0 < (Nat.choose N q : ℝ) := by
      exact_mod_cast Nat.choose_pos hq
    unfold overlapCoefficient
    split_ifs <;> positivity
  have hkernel :
      ‖genericU_N_r N r s.2 K‖ ≤ R ^ r * ‖K‖ := by
    calc
      ‖genericU_N_r N r s.2 K‖ ≤ ‖K‖ :=
        norm_genericU_N_r_le N r s.2 K
      _ = 1 * ‖K‖ := by ring
      _ ≤ R ^ r * ‖K‖ :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hR) (norm_nonneg K)
  have hnorm :
      ‖(((overlapCoefficient N p q s.1.1 : ℝ) : ℂ) •
          genericU_N_r N r s.2 K)‖ ≤
        overlapCoefficient N p q s.1.1 *
          ‖genericU_N_r N r s.2 K‖ := by
    calc
      _ ≤ ‖((overlapCoefficient N p q s.1.1 : ℝ) : ℂ)‖ *
          ‖genericU_N_r N r s.2 K‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ = overlapCoefficient N p q s.1.1 *
          ‖genericU_N_r N r s.2 K‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  calc
    _ ≤ overlapCoefficient N p q s.1.1 *
          ‖genericU_N_r N r s.2 K‖ := hnorm
    _ ≤ overlapCoefficient N p q s.1.1 * (R ^ r * ‖K‖) :=
      mul_le_mul_of_nonneg_left hkernel hc
    _ = feasibleOverlapRadiusTerm N p q R A Bop s := by
      rfl

/-- The overlap-kernel product expansion has the LOCAL-011 operator radius
bound; the coefficient sum is controlled by the frozen PlacementFiberBound
majorant. -/
theorem norm_genericU_product_le_radius
    {N p q : ℕ} {R : ℝ} (hp : p ≤ N) (hq : q ≤ N) (hR : 1 ≤ R)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    ‖(genericU_N_r N p hp A).comp (genericU_N_r N q hq Bop)‖ ≤
      (R ^ p * ‖A‖) * (R ^ q * ‖Bop‖) := by
  let T : FeasibleOverlapIndex N p q →
      SymSector ℂ H N →L[ℂ] SymSector ℂ H N := fun s =>
    (((overlapCoefficient N p q s.1.1 : ℝ) : ℂ) •
      genericU_N_r N (unionSize p q s.1.1) s.2
        (averagedOverlapKernel
          (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
          (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)) A Bop))
  rw [genericU_product_eq_overlapKernelExpansion]
  calc
    _ ≤ ∑ s : FeasibleOverlapIndex N p q, ‖T s‖ := by
      simpa using (norm_sum_le
        (Finset.univ : Finset (FeasibleOverlapIndex N p q))
        (fun s => T s))
    _ ≤ ∑ s : FeasibleOverlapIndex N p q,
          feasibleOverlapRadiusTerm N p q R A Bop s := by
      apply Finset.sum_le_sum
      intro s hs
      simpa [T] using norm_feasibleOverlapExpansionTerm_le hR A Bop s
    _ ≤ (R ^ p * ‖A‖) * (R ^ q * ‖Bop‖) :=
      feasibleOverlapRadius_sum_le hp hq hR A Bop

/-- The accepted RootOverlapCommutator proof packages the degree-pair
cancellation: disjoint placements commute, and only positive-overlap pairs
contribute to the normalized commutator. -/
theorem local011_averageCommutator_eq
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (rawSubsetAverage N p hp A).comp (rawSubsetAverage N q hq Bop) -
        (rawSubsetAverage N q hq Bop).comp (rawSubsetAverage N p hp A) =
      (((N.choose p : ℂ)⁻¹) * ((N.choose q : ℂ)⁻¹)) •
        ∑ S : PlacementSubset p (N - p), ∑ T : PlacementSubset q (N - q),
          ((rawSubsetPlacement N p hp S A).comp
              (rawSubsetPlacement N q hq T Bop) -
            (rawSubsetPlacement N q hq T Bop).comp
              (rawSubsetPlacement N p hp S A)) :=
  RootOverlapCommutator.average_commutator_eq N p q hp hq A Bop

/-- Fixed-degree LOCAL-011 scaled-commutator radius clause from the frozen
RootOverlapCommutator cancellation and bad-pair count. -/
theorem local011_fixedDegreeCommutator_radius
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (N : ℝ) *
        ‖(genericU_N_r N p hp A).comp (genericU_N_r N q hq Bop) -
          (genericU_N_r N q hq Bop).comp (genericU_N_r N p hp A)‖ ≤
      2 * (p * q : ℝ) * ‖A‖ * ‖Bop‖ :=
  RootOverlapCommutator.root_overlap_bound N p q hp hq A Bop

#print axioms canonicalPrefixAlignedRawOperatorTransport
#print axioms globallyCompressedCanonicalPrefixRawPairTerm_eq_averagedPlacement
#print axioms globallyCompressedAmbientFiberContribution_eq_averagedOverlapKernelPlacement
#print axioms genericU_product_eq_overlapKernelExpansion
#print axioms norm_genericU_product_le_radius
#print axioms local011_averageCommutator_eq
#print axioms local011_fixedDegreeCommutator_radius

end QuantumNLS.PlacementFiberPrefixAlignedTransport

end

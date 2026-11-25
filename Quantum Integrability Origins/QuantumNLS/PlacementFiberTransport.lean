/-
QuantumNLS.PlacementFiberTransport — canonical coordinates on an ambient
union fiber, followed by slot transport of its ordered operator contribution.

The frozen PlacementUnionReindex module is imported read-only.  This module
works in the canonical order type `Fin (p + (q-s))` on each actual union.
-/
import QuantumNLS.PlacementUnionReindex

set_option maxHeartbeats 5000000

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping
  QuantumNLS.PlacementUnionReindex

noncomputable section

namespace QuantumNLS.PlacementFiberTransport

private theorem indexedSubtype_val_eq_of_heq {ι α : Sort*}
    (P : ι → α → Prop) {i j : ι} (hij : i = j)
    (x : {a // P i a}) (y : {a // P j a}) (h : HEq x y) : x.1 = y.1 := by
  cases hij
  exact congrArg Subtype.val (eq_of_heq h)

private theorem indexedSubtype_heq_of_val_eq {ι α : Sort*}
    (P : ι → α → Prop) {i j : ι} (hij : i = j)
    (x : {a // P i a}) (y : {a // P j a}) (hval : x.1 = y.1) : HEq x y := by
  cases hij
  exact heq_of_eq (Subtype.ext hval)

/-- Enumerate the actual slots of a union by its canonical finite slot type.
The final cast is tied to the proved union cardinality. -/
def unionSlotEquiv {N k : ℕ} (U : Finset (Fin N)) (hU : U.card = k) :
    Fin k ≃ {i : Fin N // i ∈ U} := by
  classical
  let hcard : Fintype.card {i : Fin N // i ∈ U} = k := by simp [hU]
  exact (Equiv.cast (congrArg Fin hcard)).symm.trans
    (Fintype.equivFin {i : Fin N // i ∈ U}).symm

/-- The actual ambient-slot embedding induced by `unionSlotEquiv`. -/
def unionSlotEmbedding {N k : ℕ} (U : Finset (Fin N)) (hU : U.card = k) :
    Fin k ↪ Fin N :=
  (unionSlotEquiv U hU).toEmbedding.trans
    ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩

/-- Push a canonical local slot set into the actual ambient union. -/
def pushUnionSlots {N k : ℕ} (U : Finset (Fin N)) (hU : U.card = k)
    (S : Finset (Fin k)) : Finset (Fin N) :=
  S.map (unionSlotEmbedding U hU)

/-- Pull an ambient subset of a fixed union back to its canonical `Fin k`
coordinates. -/
def pullUnionEmbedding {N k : ℕ} (U : Finset (Fin N)) (hU : U.card = k)
    (S : Finset (Fin N)) (hS : S ⊆ U) : {x // x ∈ S} ↪ Fin k :=
  ⟨fun x => (unionSlotEquiv U hU).symm ⟨x.1, hS x.2⟩,
    fun x y h => by
      have h' : (⟨x.1, hS x.2⟩ : {i : Fin N // i ∈ U}) =
          ⟨y.1, hS y.2⟩ := (unionSlotEquiv U hU).symm.injective h
      apply Subtype.ext
      exact congrArg (fun z : {i : Fin N // i ∈ U} => z.1) h'⟩

def pullUnionSlots {N k : ℕ} (U : Finset (Fin N)) (hU : U.card = k)
    (S : Finset (Fin N)) (hS : S ⊆ U) : Finset (Fin k) :=
  S.attach.map (pullUnionEmbedding U hU S hS)

theorem pushUnionSlots_card {N k : ℕ} (U : Finset (Fin N)) (hU : U.card = k)
    (S : Finset (Fin k)) : (pushUnionSlots U hU S).card = S.card := by
  simp [pushUnionSlots]

theorem pushUnionSlots_subset {N k : ℕ} (U : Finset (Fin N))
    (hU : U.card = k) (S : Finset (Fin k)) : pushUnionSlots U hU S ⊆ U := by
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
  exact (unionSlotEquiv U hU i).2

theorem pull_pushUnionSlots {N k : ℕ} (U : Finset (Fin N))
    (hU : U.card = k) (S : Finset (Fin k)) :
    pullUnionSlots U hU (pushUnionSlots U hU S)
      (pushUnionSlots_subset U hU S) = S := by
  classical
  ext i
  change i ∈ (pushUnionSlots U hU S).attach.map
      (pullUnionEmbedding U hU (pushUnionSlots U hU S)
        (pushUnionSlots_subset U hU S)) ↔ i ∈ S
  constructor
  · intro hi
    rcases Finset.mem_map.mp hi with ⟨a, ha, hai⟩
    rcases Finset.mem_map.mp (show a.1 ∈ pushUnionSlots U hU S from a.2) with
      ⟨j, hj, hja⟩
    have hji : j = i := by
      have hval : a.1 = (unionSlotEmbedding U hU) i := by
        have h' := congrArg (unionSlotEquiv U hU) hai
        have h'' : (⟨a.1, pushUnionSlots_subset U hU S a.2⟩ :
            {x : Fin N // x ∈ U}) = unionSlotEquiv U hU i := by
          change (unionSlotEquiv U hU)
              ((unionSlotEquiv U hU).symm ⟨a.1,
                pushUnionSlots_subset U hU S a.2⟩) = _ at h'
          simpa only [Equiv.apply_symm_apply] using h'
        exact congrArg (fun z : {x : Fin N // x ∈ U} => z.1) h''
      apply (unionSlotEmbedding U hU).injective
      exact hja.trans hval
    simpa [hji] using hj
  · intro hi
    let a : {x // x ∈ pushUnionSlots U hU S} :=
      ⟨(unionSlotEmbedding U hU) i,
        Finset.mem_map.mpr ⟨i, hi, rfl⟩⟩
    have hUmem := pushUnionSlots_subset U hU S a.2
    refine Finset.mem_map.mpr ⟨a, Finset.mem_attach _ _, ?_⟩
    change (unionSlotEquiv U hU).symm
        (⟨(unionSlotEmbedding U hU) i, hUmem⟩ : {x : Fin N // x ∈ U}) = i
    have hval : (⟨(unionSlotEmbedding U hU) i, hUmem⟩ :
        {x : Fin N // x ∈ U}) = unionSlotEquiv U hU i := by
      apply Subtype.ext
      rfl
    rw [hval]
    exact Equiv.symm_apply_apply _ _

theorem pullUnionSlots_congr {N k : ℕ} (U : Finset (Fin N))
    (hU : U.card = k) {S T : Finset (Fin N)} (hST : S = T)
    (hS : S ⊆ U) (hT : T ⊆ U) :
    pullUnionSlots U hU S hS = pullUnionSlots U hU T hT := by
  cases hST
  rfl

theorem push_pullUnionSlots {N k : ℕ} (U : Finset (Fin N))
    (hU : U.card = k) (S : Finset (Fin N)) (hS : S ⊆ U) :
    pushUnionSlots U hU (pullUnionSlots U hU S hS) = S := by
  classical
  ext i
  change i ∈ (S.attach.map (pullUnionEmbedding U hU S hS)).map
      (unionSlotEmbedding U hU) ↔ i ∈ S
  constructor
  · intro hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, hji⟩
    rcases Finset.mem_map.mp hj with ⟨a, ha, haj⟩
    have hEmbed : (unionSlotEmbedding U hU) (pullUnionEmbedding U hU S hS a) = a.1 := by
      change ((unionSlotEquiv U hU)
          ((unionSlotEquiv U hU).symm ⟨a.1, hS a.2⟩)).1 = a.1
      rw [Equiv.apply_symm_apply]
    have hai : a.1 = i := by
      calc
        a.1 = (unionSlotEmbedding U hU) (pullUnionEmbedding U hU S hS a) := hEmbed.symm
        _ = (unionSlotEmbedding U hU) j := by rw [haj]
        _ = i := hji
    simpa [hai] using a.2
  · intro hi
    let a : {x // x ∈ S} := ⟨i, hi⟩
    refine Finset.mem_map.mpr ⟨pullUnionEmbedding U hU S hS a,
      Finset.mem_map.mpr ⟨a, Finset.mem_attach _ _, rfl⟩, ?_⟩
    change ((unionSlotEquiv U hU)
        ((unionSlotEquiv U hU).symm ⟨i, hS hi⟩)).1 = i
    rw [Equiv.apply_symm_apply]

theorem pushUnionSlots_union {N k : ℕ} (U : Finset (Fin N))
    (hU : U.card = k) (S T : Finset (Fin k)) :
    pushUnionSlots U hU (S ∪ T) = pushUnionSlots U hU S ∪ pushUnionSlots U hU T := by
  simp [pushUnionSlots, Finset.map_union]

theorem pushUnionSlots_inter {N k : ℕ} (U : Finset (Fin N))
    (hU : U.card = k) (S T : Finset (Fin k)) :
    pushUnionSlots U hU (S ∩ T) = pushUnionSlots U hU S ∩ pushUnionSlots U hU T := by
  simp [pushUnionSlots, Finset.map_inter]

theorem pullUnionSlots_card {N k : ℕ} (U : Finset (Fin N))
    (hU : U.card = k) (S : Finset (Fin N)) (hS : S ⊆ U) :
    (pullUnionSlots U hU S hS).card = S.card := by
  calc
    _ = (pushUnionSlots U hU (pullUnionSlots U hU S hS)).card := by
      symm
      exact pushUnionSlots_card U hU _
    _ = S.card := by rw [push_pullUnionSlots]

theorem pullUnionSlots_univ {N k : ℕ} (U : Finset (Fin N))
    (hU : U.card = k) : pullUnionSlots U hU U Finset.Subset.rfl = Finset.univ := by
  apply (pullUnionSlots U hU U Finset.Subset.rfl).card_eq_iff_eq_univ.mp
  simpa [pullUnionSlots_card]

theorem pushUnionSlots_univ {N k : ℕ} (U : Finset (Fin N))
    (hU : U.card = k) : pushUnionSlots U hU Finset.univ = U := by
  rw [← pullUnionSlots_univ U hU]
  exact push_pullUnionSlots U hU U Finset.Subset.rfl

/-- Convert a literal ambient `p`-subset into the source placement encoding
on `Fin (p + (N-p))`. -/
def sourcePlacementOfSlots {N p : ℕ} (hp : p ≤ N)
    (S : Finset (Fin N)) (hS : S.card = p) : PlacementSubset p (N - p) := by
  refine ⟨castSlotSet (Nat.add_sub_of_le hp).symm S, ?_⟩
  simp [castSlotSet, hS]

theorem castSlotSet_symm {m n : ℕ} (h : m = n) (S : Finset (Fin m)) :
    castSlotSet h.symm (castSlotSet h S) = S := by
  cases h
  simp [castSlotSet]

theorem slots_sourcePlacementOfSlots {N p : ℕ} (hp : p ≤ N)
    (S : Finset (Fin N)) (hS : S.card = p) :
    castSlotSet (Nat.add_sub_of_le hp)
      (sourcePlacementOfSlots hp S hS).1 = S := by
  change castSlotSet (Nat.add_sub_of_le hp)
      (castSlotSet (Nat.add_sub_of_le hp).symm S) = S
  exact castSlotSet_symm (Nat.add_sub_of_le hp).symm S

theorem pairPlacementKey_overlap {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (z : ActualPairPlacement N p q) :
    (pairPlacementKey hp hq z).1.1.1 =
      (leftSlots hp z ∩ rightSlots hq z).card := rfl

theorem pairPlacementKey_union {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (z : ActualPairPlacement N p q) :
    (pairPlacementKey hp hq z).1.2 = leftSlots hp z ∪ rightSlots hq z := rfl

/-- The overlap parameter stored by an ambient union key. -/
def overlapSizeOfBase {N p q : ℕ} (b : PairPlacementBase N p q) : ℕ :=
  b.1.1.1

theorem overlapLeftBound {N p q : ℕ} (b : PairPlacementBase N p q) :
    overlapSizeOfBase b ≤ p :=
  le_trans b.1.1.2 (min_le_left _ _)

theorem overlapRightBound {N p q : ℕ} (b : PairPlacementBase N p q) :
    overlapSizeOfBase b ≤ q :=
  le_trans b.1.1.2 (min_le_right _ _)

abbrev CanonicalOverlapFiber (p q s : ℕ) (_hsp : s ≤ p) (_hsq : s ≤ q) :=
  Σ S : PlacementSubset p (q - s),
    {T : Finset (Fin (p + (q - s))) // T ∈ overlapFiber S.1 q s}

/-- Pull an ambient pair in one literal union fiber into canonical local
`Fin (p+(q-s))` coordinates.  The source placement encoding is uncast on
input and output explicitly through `castSlotSet`/`sourcePlacementOfSlots`.
-/
noncomputable def ambientFiberToCanonical {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q) :
    pairUnionFiber hp hq b →
      CanonicalOverlapFiber p q (overlapSizeOfBase b)
        (overlapLeftBound b) (overlapRightBound b) := by
  classical
  intro z
  let s := overlapSizeOfBase b
  let U := b.1.2
  have hU : U.card = p + (q - s) := by
    simpa [s, overlapSizeOfBase, unionSize] using b.2
  let S := leftSlots hp z.1
  let T := rightSlots hq z.1
  have hbase : (pairPlacementKey hp hq z.1).1 = b.1 :=
    congrArg Subtype.val z.2
  have hI : (S ∩ T).card = s := by
    have h := congrArg (fun x :
        ({u : ℕ // u ≤ min p q} × Finset (Fin N)) => x.1.1) hbase
    simpa [S, T, s, overlapSizeOfBase, pairPlacementKey_overlap] using h
  have hUeq : S ∪ T = U := by
    have h := congrArg Prod.snd hbase
    simpa [S, T, U, pairPlacementKey_union] using h
  have hSsub : S ⊆ U := by rw [← hUeq]; exact Finset.subset_union_left
  have hTsub : T ⊆ U := by rw [← hUeq]; exact Finset.subset_union_right
  have hScard : S.card = p := by
    simpa [S, leftSlots, castSlotSet] using z.1.1.2
  have hTcard : T.card = q := by
    simpa [T, rightSlots, castSlotSet] using z.1.2.2
  let SL : PlacementSubset p (q - s) :=
    ⟨pullUnionSlots U hU S hSsub, by
      simpa [unionSize] using
        (pullUnionSlots_card U hU S hSsub).trans hScard⟩
  let TL : Finset (Fin (p + (q - s))) := pullUnionSlots U hU T hTsub
  have hTLcard : TL.card = q := by
    dsimp [TL]
    simpa [unionSize] using (pullUnionSlots_card U hU T hTsub).trans hTcard
  have hPushS : pushUnionSlots U hU SL.1 = S := by
    dsimp [SL]
    exact push_pullUnionSlots U hU S hSsub
  have hPushT : pushUnionSlots U hU TL = T := by
    dsimp [TL]
    exact push_pullUnionSlots U hU T hTsub
  have hLocalInter : (SL.1 ∩ TL).card = s := by
    calc
      _ = (pushUnionSlots U hU (SL.1 ∩ TL)).card := by
        symm
        exact pushUnionSlots_card U hU _
      _ = (pushUnionSlots U hU SL.1 ∩ pushUnionSlots U hU TL).card := by
        rw [pushUnionSlots_inter]
      _ = s := by rw [hPushS, hPushT, hI]
  have hLocalFiber : TL ∈ overlapFiber SL.1 q s := by
    rw [overlapFiber, Finset.mem_filter]
    exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTLcard⟩,
      hLocalInter⟩
  exact ⟨SL, ⟨TL, hLocalFiber⟩⟩

theorem overlapConfigurationFiberEquiv_leftSlots {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq) :
    ((overlapConfigurationFiberEquiv hsp hsq C).1) = C.left := rfl

theorem overlapConfigurationFiberEquiv_rightSlots {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq) :
    ((overlapConfigurationFiberEquiv hsp hsq C).2.1) =
      C.right.1.map (overlapSlotEquiv hsp hsq).toEmbedding := rfl

theorem ambientFiberToCanonical_leftSlots {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (z : pairUnionFiber hp hq b) :
    (ambientFiberToCanonical hp hq b z).1.1 =
      pullUnionSlots b.1.2
        (by simpa [overlapSizeOfBase, unionSize] using b.2)
        (leftSlots hp z.1)
        (by
          have hbase := congrArg Subtype.val z.2
          have hu := congrArg Prod.snd hbase
          rw [← hu]
          exact Finset.subset_union_left) := by
  rfl

theorem ambientFiberToCanonical_rightSlots {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (z : pairUnionFiber hp hq b) :
    (ambientFiberToCanonical hp hq b z).2.1 =
      pullUnionSlots b.1.2
        (by simpa [overlapSizeOfBase, unionSize] using b.2)
        (rightSlots hq z.1)
        (by
          have hbase := congrArg Subtype.val z.2
          have hu := congrArg Prod.snd hbase
          rw [← hu]
          exact Finset.subset_union_right) := by
  rfl

theorem pairFiber_left_subset_union {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (z : pairUnionFiber hp hq b) : leftSlots hp z.1 ⊆ b.1.2 := by
  have hbase := congrArg Subtype.val z.2
  have hUnion := congrArg Prod.snd hbase
  have h : leftSlots hp z.1 ∪ rightSlots hq z.1 = b.1.2 := by
    simpa [pairPlacementKey_union] using hUnion
  rw [← h]
  exact Finset.subset_union_left

theorem pairFiber_right_subset_union {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (z : pairUnionFiber hp hq b) : rightSlots hq z.1 ⊆ b.1.2 := by
  have hbase := congrArg Subtype.val z.2
  have hUnion := congrArg Prod.snd hbase
  have h : leftSlots hp z.1 ∪ rightSlots hq z.1 = b.1.2 := by
    simpa [pairPlacementKey_union] using hUnion
  rw [← h]
  exact Finset.subset_union_right

/-- Push a canonical overlap configuration onto the specified actual union
and recast its two placements into the frozen source `PlacementSubset` types.
-/
noncomputable def canonicalToAmbientPair {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q) :
    OverlapConfiguration p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b) → ActualPairPlacement N p q := by
  classical
  intro C
  let s := overlapSizeOfBase b
  let U := b.1.2
  have hU : U.card = p + (q - s) := by
    simpa [s, overlapSizeOfBase, unionSize] using b.2
  let R : Finset (Fin (p + (q - s))) :=
    C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
      (overlapRightBound b)).toEmbedding
  let SA := pushUnionSlots U hU C.left.1
  let TA := pushUnionSlots U hU R
  have hRcard : R.card = q := by
    dsimp [R]
    simp [C.right.2]
  have hScard : SA.card = p := by
    dsimp [SA]
    rw [pushUnionSlots_card]
    exact C.left.2
  have hTcard : TA.card = q := by
    dsimp [TA]
    rw [pushUnionSlots_card]
    exact hRcard
  exact (sourcePlacementOfSlots hp SA hScard,
    sourcePlacementOfSlots hq TA hTcard)

theorem canonicalToAmbientPair_leftSlots {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (C : OverlapConfiguration p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b)) :
    leftSlots hp (canonicalToAmbientPair hp hq b C) =
      pushUnionSlots b.1.2
        (by simpa [overlapSizeOfBase, unionSize] using b.2) C.left.1 := by
  have hU : b.1.2.card = p + (q - overlapSizeOfBase b) := by
    simpa [overlapSizeOfBase, unionSize] using b.2
  have hcard : (pushUnionSlots b.1.2 hU C.left.1).card = p := by
    rw [pushUnionSlots_card]
    exact C.left.2
  change castSlotSet (Nat.add_sub_of_le hp)
      (sourcePlacementOfSlots hp (pushUnionSlots b.1.2 hU C.left.1) hcard).1 = _
  exact slots_sourcePlacementOfSlots hp _ hcard

theorem canonicalToAmbientPair_rightSlots {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (C : OverlapConfiguration p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b)) :
    rightSlots hq (canonicalToAmbientPair hp hq b C) =
      pushUnionSlots b.1.2
        (by simpa [overlapSizeOfBase, unionSize] using b.2)
        (C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
          (overlapRightBound b)).toEmbedding) := by
  have hU : b.1.2.card = p + (q - overlapSizeOfBase b) := by
    simpa [overlapSizeOfBase, unionSize] using b.2
  let R : Finset (Fin (p + (q - overlapSizeOfBase b))) :=
    C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
      (overlapRightBound b)).toEmbedding
  have hRcard : R.card = q := by dsimp [R]; simp [C.right.2]
  have hcard : (pushUnionSlots b.1.2 hU R).card = q := by
    rw [pushUnionSlots_card]
    exact hRcard
  change castSlotSet (Nat.add_sub_of_le hq)
      (sourcePlacementOfSlots hq (pushUnionSlots b.1.2 hU R) hcard).1 = _
  exact slots_sourcePlacementOfSlots hq _ hcard

theorem sourcePlacementOfLeftSlots {N p q : ℕ} (hp : p ≤ N)
    (z : ActualPairPlacement N p q) :
    sourcePlacementOfSlots hp (leftSlots hp z)
      (by simpa [leftSlots, castSlotSet] using z.1.2) = z.1 := by
  apply Subtype.ext
  change castSlotSet (Nat.add_sub_of_le hp).symm
      (castSlotSet (Nat.add_sub_of_le hp) z.1.1) = z.1.1
  exact castSlotSet_symm (Nat.add_sub_of_le hp) z.1.1

theorem sourcePlacementOfRightSlots {N p q : ℕ} (hq : q ≤ N)
    (z : ActualPairPlacement N p q) :
    sourcePlacementOfSlots hq (rightSlots hq z)
      (by simpa [rightSlots, castSlotSet] using z.2.2) = z.2 := by
  apply Subtype.ext
  change castSlotSet (Nat.add_sub_of_le hq).symm
      (castSlotSet (Nat.add_sub_of_le hq) z.2.1) = z.2.1
  exact castSlotSet_symm (Nat.add_sub_of_le hq) z.2.1

theorem canonicalToAmbientPair_key {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (C : OverlapConfiguration p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b)) :
    pairPlacementKey hp hq (canonicalToAmbientPair hp hq b C) = b := by
  classical
  let s := overlapSizeOfBase b
  let U := b.1.2
  have hU : U.card = p + (q - s) := by
    simpa [s, overlapSizeOfBase, unionSize] using b.2
  let R : Finset (Fin (p + (q - s))) :=
    C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
      (overlapRightBound b)).toEmbedding
  let SA := pushUnionSlots U hU C.left.1
  let TA := pushUnionSlots U hU R
  have hScard : SA.card = p := by
    dsimp [SA]
    rw [pushUnionSlots_card]
    exact C.left.2
  have hRcard : R.card = q := by dsimp [R]; simp [C.right.2]
  have hTcard : TA.card = q := by dsimp [TA]; rw [pushUnionSlots_card]; exact hRcard
  have hleft : leftSlots hp (canonicalToAmbientPair hp hq b C) = SA := by
    change castSlotSet (Nat.add_sub_of_le hp)
        (sourcePlacementOfSlots hp SA hScard).1 = SA
    exact slots_sourcePlacementOfSlots hp SA hScard
  have hright : rightSlots hq (canonicalToAmbientPair hp hq b C) = TA := by
    change castSlotSet (Nat.add_sub_of_le hq)
        (sourcePlacementOfSlots hq TA hTcard).1 = TA
    exact slots_sourcePlacementOfSlots hq TA hTcard
  have hinter : (SA ∩ TA).card = s := by
    calc
      _ = (pushUnionSlots U hU (C.left.1 ∩ R)).card := by
        rw [pushUnionSlots_inter]
      _ = (C.left.1 ∩ R).card := by rw [pushUnionSlots_card]
      _ = s := C.overlap_card
  have hunion : SA ∪ TA = U := by
    have hcover : C.left.1 ∪ R = Finset.univ := by
      simpa [R] using C.covers_union
    calc
      SA ∪ TA = pushUnionSlots U hU (C.left.1 ∪ R) := by
        symm
        exact pushUnionSlots_union U hU C.left.1 R
      _ = pushUnionSlots U hU Finset.univ := by rw [hcover]
      _ = U := pushUnionSlots_univ U hU
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rw [pairPlacementKey_overlap, hleft, hright]
    exact hinter
  · rw [pairPlacementKey_union, hleft, hright]
    exact hunion

noncomputable def canonicalToAmbientFiber {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q) :
    OverlapConfiguration p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b) → pairUnionFiber hp hq b := by
  intro C
  exact ⟨canonicalToAmbientPair hp hq b C,
    canonicalToAmbientPair_key hp hq b C⟩

noncomputable def ambientFiberToOverlapConfiguration {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q) :
    pairUnionFiber hp hq b → OverlapConfiguration p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b) :=
  (overlapConfigurationFiberEquiv (overlapLeftBound b)
    (overlapRightBound b)).symm ∘ ambientFiberToCanonical hp hq b

noncomputable def overlapConfigurationToAmbientFiber {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q) :
    OverlapConfiguration p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b) → pairUnionFiber hp hq b :=
  canonicalToAmbientFiber hp hq b

private theorem localPair_union_eq_univ {N p q s : ℕ}
    (S T : Finset (Fin N)) (hS : S.card = p) (hT : T.card = q)
    (hI : (S ∩ T).card = s) (hN : N = p + q - s) :
    S ∪ T = Finset.univ := by
  apply (S ∪ T).card_eq_iff_eq_univ.mp
  have hcard := Finset.card_inter_add_card_union S T
  rw [hS, hT, hI] at hcard
  have hU : (S ∪ T).card = N := by omega
  simpa using hU

/-- Explicitly recover an overlap configuration from canonical left and
right slots. -/
noncomputable def canonicalToOverlapConfiguration {p q s : ℕ}
    (hsp : s ≤ p) (hsq : s ≤ q)
    (y : CanonicalOverlapFiber p q s hsp hsq) :
    OverlapConfiguration p q s hsp hsq := by
  classical
  rcases y with ⟨S, ⟨Q, hQ⟩⟩
  have hQcard : Q ∈ Finset.univ.powersetCard q :=
    (Finset.mem_filter.mp hQ).1
  have hI : (S.1 ∩ Q).card = s := (Finset.mem_filter.mp hQ).2
  let e := overlapSlotEquiv hsp hsq
  let R := Q.map e.symm.toEmbedding
  let Rlocal := R.map e.toEmbedding
  have hRcard : R.card = q := by
    change (Q.map e.symm.toEmbedding).card = q
    rw [Finset.card_map]
    exact (Finset.mem_powersetCard.mp hQcard).2
  have hmap : R.map e.toEmbedding = Q := by
    change (Q.map e.symm.toEmbedding).map e.toEmbedding = Q
    rw [Finset.map_map]
    simp [e]
  have hRlocalCard : Rlocal.card = q := by simp [Rlocal, hRcard]
  have hcover : S.1 ∪ Rlocal = Finset.univ := by
    apply localPair_union_eq_univ (s := s) S.1 Rlocal S.2 hRlocalCard ?_ (by omega)
    change (S.1 ∩ R.map e.toEmbedding).card = s
    rw [hmap]
    exact hI
  refine ⟨S, ⟨R, hRcard⟩, ?_, hcover⟩
  · rw [hmap]
    exact hI

theorem overlapConfigurationFiberEquiv_canonicalToOverlapConfiguration
    {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (y : CanonicalOverlapFiber p q s hsp hsq) :
    overlapConfigurationFiberEquiv hsp hsq
      (canonicalToOverlapConfiguration hsp hsq y) = y := by
  classical
  rcases y with ⟨S, ⟨Q, hQ⟩⟩
  rw [overlapFiber, Finset.mem_filter] at hQ
  rcases hQ with ⟨hQcard, hI⟩
  let e := overlapSlotEquiv hsp hsq
  let R := Q.map e.symm.toEmbedding
  have hmap : R.map e.toEmbedding = Q := by
    change (Q.map e.symm.toEmbedding).map e.toEmbedding = Q
    rw [Finset.map_map]
    simp [e]
  let C := canonicalToOverlapConfiguration hsp hsq
    (⟨S, ⟨Q, hQ⟩⟩ : CanonicalOverlapFiber p q s hsp hsq)
  have hleftC : C.left = S := by
    dsimp [C, canonicalToOverlapConfiguration]
  have hfirst : (overlapConfigurationFiberEquiv hsp hsq C).1 = S := by
    rw [overlapConfigurationFiberEquiv_leftSlots]
    exact hleftC
  let targetRight : {R : Finset (Fin (p + (q - s))) //
      R ∈ overlapFiber S.1 q s} := ⟨Q, hQ⟩
  have hsecond : (overlapConfigurationFiberEquiv hsp hsq C).2.1 = Q := by
    calc
      _ = C.right.1.map e.toEmbedding := overlapConfigurationFiberEquiv_rightSlots hsp hsq C
      _ = Q := by
        dsimp [C, canonicalToOverlapConfiguration, R]
        exact hmap
  apply Sigma.ext hfirst
  exact indexedSubtype_heq_of_val_eq
    (fun X R => R ∈ overlapFiber X.1 q s) hfirst
    (overlapConfigurationFiberEquiv hsp hsq C).2 targetRight hsecond

/-- Build the ambient source pair from the canonical sigma presentation of a
local overlap configuration. -/
noncomputable def canonicalSigmaToAmbientFiber {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q) :
    CanonicalOverlapFiber p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b) → pairUnionFiber hp hq b :=
  fun y => canonicalToAmbientFiber hp hq b
    (canonicalToOverlapConfiguration (overlapLeftBound b)
      (overlapRightBound b) y)

/-- The pull/push slot maps invert on an ambient pair fiber. -/
private theorem ambientFiberCanonical_left_inv {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (z : pairUnionFiber hp hq b) :
    canonicalSigmaToAmbientFiber hp hq b (ambientFiberToCanonical hp hq b z) = z := by
    apply Subtype.ext
    rcases z with ⟨⟨S, T⟩, hz⟩
    let z₀ : pairUnionFiber hp hq b := ⟨(S, T), hz⟩
    let zRaw : {z : ActualPairPlacement N p q // pairPlacementKey hp hq z = b} :=
      ⟨(S, T), hz⟩
    let y := ambientFiberToCanonical hp hq b zRaw
    rcases hy : y with ⟨YL, ⟨YR, hYR⟩⟩
    let e := overlapConfigurationFiberEquiv (overlapLeftBound b)
      (overlapRightBound b)
    let C := canonicalToOverlapConfiguration (overlapLeftBound b)
      (overlapRightBound b) y
    have hC : e C = y :=
      overlapConfigurationFiberEquiv_canonicalToOverlapConfiguration
        (overlapLeftBound b) (overlapRightBound b) y
    rw [hy] at hC
    have hmem : C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
        (overlapRightBound b)).toEmbedding ∈ overlapFiber C.left.1 q
          (overlapSizeOfBase b) := by
      rw [overlapFiber, Finset.mem_filter]
      exact ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, by simpa using C.right.2⟩, C.overlap_card⟩
    let localRight : {R : Finset (Fin (p + (q - overlapSizeOfBase b))) //
        R ∈ overlapFiber C.left.1 q (overlapSizeOfBase b)} :=
      ⟨C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
        (overlapRightBound b)).toEmbedding, hmem⟩
    let localSigma : CanonicalOverlapFiber p q (overlapSizeOfBase b)
        (overlapLeftBound b) (overlapRightBound b) := ⟨C.left, localRight⟩
    let targetRight : {R : Finset (Fin (p + (q - overlapSizeOfBase b))) //
        R ∈ overlapFiber YL.1 q (overlapSizeOfBase b)} := ⟨YR, hYR⟩
    let targetSigma : CanonicalOverlapFiber p q (overlapSizeOfBase b)
        (overlapLeftBound b) (overlapRightBound b) := ⟨YL, targetRight⟩
    change localSigma = targetSigma at hC
    dsimp [localSigma, targetSigma, localRight, targetRight] at hC
    simp only [Sigma.mk.inj_iff] at hC
    rcases hC with ⟨hfirst, hright⟩
    cases hfirst
    have hrightEq := eq_of_heq hright
    have hrightC : C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
        (overlapRightBound b)).toEmbedding = YR := congrArg Subtype.val hrightEq
    have hU : b.1.2.card = p + (q - overlapSizeOfBase b) := by
      simpa [overlapSizeOfBase, unionSize] using b.2
    have hyLeft : y.1.1 = C.left.1 :=
      congrArg (fun v : CanonicalOverlapFiber p q (overlapSizeOfBase b)
        (overlapLeftBound b) (overlapRightBound b) => v.1.1) hy
    have hleftPull := ambientFiberToCanonical_leftSlots hp hq b zRaw
    have hleftCanonical : C.left.1 =
        pullUnionSlots b.1.2 hU (leftSlots hp zRaw.1)
          (pairFiber_left_subset_union hp hq b zRaw) := hyLeft.symm.trans hleftPull
    have hleftSlots : pushUnionSlots b.1.2 hU C.left.1 = leftSlots hp zRaw.1 := by
      calc
        _ = pushUnionSlots b.1.2 hU
            (pullUnionSlots b.1.2 hU (leftSlots hp zRaw.1)
              (pairFiber_left_subset_union hp hq b zRaw)) :=
              congrArg (pushUnionSlots b.1.2 hU) hleftCanonical
        _ = leftSlots hp zRaw.1 := push_pullUnionSlots _ _ _ _
    have hrightSlots : pushUnionSlots b.1.2 hU
        (C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
          (overlapRightBound b)).toEmbedding) = rightSlots hq zRaw.1 := by
      have hyRight : YR = y.2.1 :=
        (congrArg (fun v : CanonicalOverlapFiber p q (overlapSizeOfBase b)
          (overlapLeftBound b) (overlapRightBound b) => v.2.1) hy).symm
      have hrightPull := ambientFiberToCanonical_rightSlots hp hq b zRaw
      calc
        _ = pushUnionSlots b.1.2 hU
            (pullUnionSlots b.1.2 hU (rightSlots hq zRaw.1)
              (pairFiber_right_subset_union hp hq b zRaw)) :=
              congrArg (pushUnionSlots b.1.2 hU) (hrightC.trans hyRight |>.trans hrightPull)
        _ = rightSlots hq zRaw.1 := push_pullUnionSlots _ _ _ _
    have hcardLeft : (pushUnionSlots b.1.2 hU C.left.1).card = p := by
      rw [pushUnionSlots_card]
      exact C.left.2
    have hcardRight : (pushUnionSlots b.1.2 hU
        (C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
          (overlapRightBound b)).toEmbedding)).card = q := by
      rw [pushUnionSlots_card]
      simp [C.right.2]
    have hsourceLeft :
        sourcePlacementOfSlots hp (pushUnionSlots b.1.2 hU C.left.1) hcardLeft =
          sourcePlacementOfSlots hp (leftSlots hp zRaw.1)
            (by simpa [leftSlots, castSlotSet] using zRaw.1.1.2) := by
      apply Subtype.ext
      change castSlotSet (Nat.add_sub_of_le hp).symm
          (pushUnionSlots b.1.2 hU C.left.1) =
        castSlotSet (Nat.add_sub_of_le hp).symm (leftSlots hp zRaw.1)
      exact congrArg (castSlotSet (Nat.add_sub_of_le hp).symm) hleftSlots
    have hsourceRight :
        sourcePlacementOfSlots hq (pushUnionSlots b.1.2 hU
          (C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
            (overlapRightBound b)).toEmbedding)) hcardRight =
          sourcePlacementOfSlots hq (rightSlots hq zRaw.1)
            (by simpa [rightSlots, castSlotSet] using zRaw.1.2.2) := by
      apply Subtype.ext
      change castSlotSet (Nat.add_sub_of_le hq).symm
          (pushUnionSlots b.1.2 hU
            (C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
              (overlapRightBound b)).toEmbedding)) =
        castSlotSet (Nat.add_sub_of_le hq).symm (rightSlots hq zRaw.1)
      exact congrArg (castSlotSet (Nat.add_sub_of_le hq).symm) hrightSlots
    apply Prod.ext
    · exact hsourceLeft.trans (sourcePlacementOfLeftSlots hp zRaw.1)
    · exact hsourceRight.trans (sourcePlacementOfRightSlots hq zRaw.1)
/-- The pull/push slot maps also invert on canonical local fibers. -/
private theorem ambientFiberCanonical_right_inv {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q)
    (y : CanonicalOverlapFiber p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b)) :
    ambientFiberToCanonical hp hq b (canonicalSigmaToAmbientFiber hp hq b y) = y := by
    rcases y with ⟨S, ⟨T, hT⟩⟩
    let y₀ : CanonicalOverlapFiber p q (overlapSizeOfBase b)
        (overlapLeftBound b) (overlapRightBound b) := ⟨S, ⟨T, hT⟩⟩
    let e := overlapConfigurationFiberEquiv (overlapLeftBound b)
      (overlapRightBound b)
    let C := canonicalToOverlapConfiguration (overlapLeftBound b)
      (overlapRightBound b) y₀
    let z := canonicalSigmaToAmbientFiber hp hq b y₀
    have hC : e C = y₀ :=
      overlapConfigurationFiberEquiv_canonicalToOverlapConfiguration
        (overlapLeftBound b) (overlapRightBound b) y₀
    have hmem : C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
        (overlapRightBound b)).toEmbedding ∈ overlapFiber C.left.1 q
          (overlapSizeOfBase b) := by
      rw [overlapFiber, Finset.mem_filter]
      exact ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, by simpa using C.right.2⟩, C.overlap_card⟩
    let localRight : {R : Finset (Fin (p + (q - overlapSizeOfBase b))) //
        R ∈ overlapFiber C.left.1 q (overlapSizeOfBase b)} :=
      ⟨C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
        (overlapRightBound b)).toEmbedding, hmem⟩
    let localSigma : CanonicalOverlapFiber p q (overlapSizeOfBase b)
        (overlapLeftBound b) (overlapRightBound b) := ⟨C.left, localRight⟩
    let targetRight : {R : Finset (Fin (p + (q - overlapSizeOfBase b))) //
        R ∈ overlapFiber S.1 q (overlapSizeOfBase b)} := ⟨T, hT⟩
    let targetSigma : CanonicalOverlapFiber p q (overlapSizeOfBase b)
        (overlapLeftBound b) (overlapRightBound b) := ⟨S, targetRight⟩
    change localSigma = targetSigma at hC
    dsimp [localSigma, targetSigma, localRight, targetRight] at hC
    simp only [Sigma.mk.inj_iff] at hC
    rcases hC with ⟨hfirst, hright⟩
    have hrightC : C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
        (overlapRightBound b)).toEmbedding = T :=
      @indexedSubtype_val_eq_of_heq (PlacementSubset p (q - overlapSizeOfBase b))
        (Finset (Fin (p + (q - overlapSizeOfBase b))))
        (fun X R => R ∈ overlapFiber X.1 q (overlapSizeOfBase b)) C.left S hfirst
        localRight targetRight hright
    have hU : b.1.2.card = p + (q - overlapSizeOfBase b) := by
      simpa [overlapSizeOfBase, unionSize] using b.2
    have hleftSlots : leftSlots hp z.1 = pushUnionSlots b.1.2 hU C.left.1 := by
      change leftSlots hp (canonicalToAmbientPair hp hq b C) = _
      exact canonicalToAmbientPair_leftSlots hp hq b C
    have hrightSlots : rightSlots hq z.1 = pushUnionSlots b.1.2 hU
        (C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
          (overlapRightBound b)).toEmbedding) := by
      change rightSlots hq (canonicalToAmbientPair hp hq b C) = _
      rw [canonicalToAmbientPair_rightSlots hp hq b C]
    
    have houtLeft : (ambientFiberToCanonical hp hq b z).1 = S := by
      apply Subtype.ext
      change pullUnionSlots b.1.2 hU (leftSlots hp z.1)
          (pairFiber_left_subset_union hp hq b z) = S.1
      calc
        _ = pullUnionSlots b.1.2 hU (pushUnionSlots b.1.2 hU C.left.1)
            (pushUnionSlots_subset b.1.2 hU C.left.1) := by
              exact pullUnionSlots_congr _ _ hleftSlots _ _
        _ = C.left.1 := pull_pushUnionSlots _ _ _
        _ = S.1 := congrArg Subtype.val hfirst
    have houtRight : (ambientFiberToCanonical hp hq b z).2.1 = T := by
      change pullUnionSlots b.1.2 hU (rightSlots hq z.1)
          (pairFiber_right_subset_union hp hq b z) = T
      calc
        _ = pullUnionSlots b.1.2 hU
            (pushUnionSlots b.1.2 hU
              (C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
                (overlapRightBound b)).toEmbedding))
            (pushUnionSlots_subset b.1.2 hU _) := by
              exact pullUnionSlots_congr _ _ hrightSlots _ _
        _ = C.right.1.map (overlapSlotEquiv (overlapLeftBound b)
              (overlapRightBound b)).toEmbedding := pull_pushUnionSlots _ _ _
        _ = T := hrightC
    apply Sigma.ext houtLeft
    exact indexedSubtype_heq_of_val_eq
      (fun X R => R ∈ overlapFiber X.1 q (overlapSizeOfBase b))
      houtLeft (ambientFiberToCanonical hp hq b z).2 targetRight houtRight

/-- Every ambient overlap fiber is genuinely equivalent to the canonical
finite sigma of local placements. -/
noncomputable def ambientFiberCanonicalEquiv {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q) :
    pairUnionFiber hp hq b ≃ CanonicalOverlapFiber p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b) where
  toFun := ambientFiberToCanonical hp hq b
  invFun := canonicalSigmaToAmbientFiber hp hq b
  left_inv := ambientFiberCanonical_left_inv hp hq b
  right_inv := ambientFiberCanonical_right_inv hp hq b

/-- The requested equivalence with the canonical `OverlapConfiguration`
indices, obtained by composing the proved slot-set equivalence with the
frozen local fiber equivalence. -/
noncomputable def ambientFiberOverlapEquiv {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) (b : PairPlacementBase N p q) :
    pairUnionFiber hp hq b ≃ OverlapConfiguration p q (overlapSizeOfBase b)
      (overlapLeftBound b) (overlapRightBound b) :=
  (ambientFiberCanonicalEquiv hp hq b).trans
    (overlapConfigurationFiberEquiv (overlapLeftBound b)
      (overlapRightBound b)).symm

/-- Reindex the complete source pair family directly by ambient union keys
and canonical local `OverlapConfiguration` data. -/
noncomputable def pairPlacementCanonicalUnionEquiv {N p q : ℕ}
    (hp : p ≤ N) (hq : q ≤ N) :
    ActualPairPlacement N p q ≃
      Σ b : PairPlacementBase N p q,
        OverlapConfiguration p q (overlapSizeOfBase b)
          (overlapLeftBound b) (overlapRightBound b) :=
  (pairPlacementUnionEquiv N p q hp hq).trans
    (Equiv.sigmaCongrRight fun b => ambientFiberOverlapEquiv hp hq b)

/-- The actual compressed pair-operator sum, reindexed by the canonical local
overlap configurations on each literal ambient union. This retains the
ambient pair operators; the subsequent slot-transport identity is separate. -/
theorem actualPairOperatorSum_eq_canonicalConfigurationSum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    (∑ z : ActualPairPlacement N p q,
      (arbitraryNSectorSubsetPlacement N p hp z.1 A).comp
        (arbitraryNSectorSubsetPlacement N q hq z.2 B)) =
      ∑ y : Σ b : PairPlacementBase N p q,
          OverlapConfiguration p q (overlapSizeOfBase b)
            (overlapLeftBound b) (overlapRightBound b),
        (arbitraryNSectorSubsetPlacement N p hp
            ((pairPlacementCanonicalUnionEquiv hp hq).symm y).1 A).comp
          (arbitraryNSectorSubsetPlacement N q hq
            ((pairPlacementCanonicalUnionEquiv hp hq).symm y).2 B) := by
  classical
  let E := pairPlacementCanonicalUnionEquiv hp hq
  let F := fun z : ActualPairPlacement N p q =>
    (arbitraryNSectorSubsetPlacement N p hp z.1 A).comp
      (arbitraryNSectorSubsetPlacement N q hq z.2 B)
  simpa [E, F] using
    (Equiv.sum_comp E (fun y => F (E.symm y)))

end QuantumNLS.PlacementFiberTransport

/-
QuantumNLS.PlacementFiberPrefixCompression — compressed reduction of the
canonical-prefix raw-term identity for LOCAL-011.

The frozen slot bridge supplies an ambient permutation aligning each pair's
slot sets with the ordered prefix.  Global symmetric compression removes that
permutation.  This module proves the remaining reduction to the ordered raw
operator transport, but does not assume or claim that transport.
-/
import QuantumNLS.PlacementFiberPrefixSlotTransport

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

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixCompression

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private def localRightSlots {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq) : Finset (Fin (p + (q - s))) :=
  C.right.1.map (overlapSlotEquiv hsp hsq).toEmbedding

/-- The precise ordered transport still required after the frozen bridge has
aligned both local slot sets with the ambient prefix.  This is a proposition
to be proved from the placement definitions; it is not supplied to any
closed theorem below. -/
def canonicalPrefixAlignedRawOperatorTransportGap
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) : Prop :=
  ∀ C : OverlapConfiguration p q
      (overlapSizeOfBase (canonicalPrefixPairBase b))
      (overlapLeftBound (canonicalPrefixPairBase b))
      (overlapRightBound (canonicalPrefixPairBase b)),
    ∀ σ : Equiv.Perm (Fin N),
      leftSlots hp (relabelActualPair hp hq σ
        (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C)) =
        C.left.1.map (Fin.castLEEmb
          (pairPlacementBase_unionSize_le_N (canonicalPrefixPairBase b))) →
      rightSlots hq (relabelActualPair hp hq σ
        (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C)) =
        (localRightSlots (overlapLeftBound (canonicalPrefixPairBase b))
          (overlapRightBound (canonicalPrefixPairBase b)) C).map
          (Fin.castLEEmb
            (pairPlacementBase_unionSize_le_N (canonicalPrefixPairBase b))) →
      ambientRawPairOperator N p q hp hq
          (relabelActualPair hp hq σ
            (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C)) A Bop =
        castTensorOperator
          (Nat.add_sub_of_le
            (pairPlacementBase_unionSize_le_N (canonicalPrefixPairBase b)))
          (prefixTensorLift (H := H)
            (r := unionSize p q
              (overlapSizeOfBase (canonicalPrefixPairBase b)))
            (t := N - unionSize p q
              (overlapSizeOfBase (canonicalPrefixPairBase b)))
            ((subsetPlacement C.left A).comp (rightPlacement C Bop)))

private def prefixInitialPlacementSubset (r t : ℕ) : PlacementSubset r t :=
  ⟨firstPositions (p := r) (q := t), card_firstPositions r t⟩

private theorem subsetPlacement_prefixInitial_eq_firstPlacement
    {r t : ℕ} (K : BoundedSymmetricKernel H r) :
    subsetPlacement (prefixInitialPlacementSubset r t) K =
      firstPlacement (q := t) K := by
  let S := prefixInitialPlacementSubset r t
  have hrep := subsetRepresentative_maps S
  have hstable :
      (firstPositions (p := r) (q := t)).map
          (subsetRepresentative S).toEmbedding = firstPositions (p := r) (q := t) := by
    change (placementSubsetOfPerm (subsetRepresentative S)).1 = _
    rw [hrep]
    rfl
  obtain ⟨π, ρ, hblock⟩ :=
    exists_blockPerm_of_firstPositions_stable (subsetRepresentative S) hstable
  calc
    subsetPlacement S K = permutedPlacement (subsetRepresentative S) K :=
      (permutedPlacement_eq_subsetPlacement (subsetRepresentative S) S hrep K).symm
    _ = permutedPlacement (blockPerm π ρ) K := by rw [hblock]
    _ = firstPlacement (q := t) K := permutedPlacement_blockPerm_eq π ρ K

omit [CompleteSpace H] in
private theorem castSymmetricCompression_eq
    {m n : ℕ} (h : m = n)
    (T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) :
    castSymSectorOperator h
        ((symProjToSector m).comp (T.comp (SymSector ℂ H m).subtypeL)) =
      (symProjToSector n).comp
        ((castTensorOperator h T).comp (SymSector ℂ H n).subtypeL) := by
  cases h
  rfl

private theorem equivCastFin_val {m n : ℕ} (h : m = n) (i : Fin m) :
    (Equiv.cast (congrArg Fin h) i).val = i.val := by
  cases h
  rfl

private theorem castPrefixSlots_eq_firstPositions
    {N r : ℕ} (hr : r ≤ N) :
    castSlotSet (Nat.add_sub_of_le hr).symm (canonicalPrefixSlots hr) =
      firstPositions (p := r) (q := N - r) := by
  change Finset.map
      (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hr).symm)).toEmbedding
        (Finset.univ.map (Fin.castLEEmb hr)) =
      Finset.univ.map (Fin.castAddEmb (N - r))
  rw [Finset.map_map]
  congr 1
  ext i
  change (Equiv.cast (congrArg Fin (Nat.add_sub_of_le hr).symm)
      (Fin.castLE hr i)).val = (Fin.castAdd (N - r) i).val
  rw [equivCastFin_val]
  simp
  exact (Nat.add_sub_of_le hr).symm

/-- The N-independent averaged kernel, placed on the canonical prefix, is
the global compression of the lifted local fusion operator. -/
private theorem averagedPrefixPlacement_eq_compressedFusion
    {N p q : ℕ} (b : PairPlacementBase N p q)
    (C : OverlapConfiguration p q
      (overlapSizeOfBase (canonicalPrefixPairBase b))
      (overlapLeftBound (canonicalPrefixPairBase b))
      (overlapRightBound (canonicalPrefixPairBase b)))
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    averagedOverlapKernelPlacement N p q (canonicalPrefixPairBase b) A Bop =
      castSymSectorOperator
        (Nat.add_sub_of_le (pairPlacementBase_unionSize_le_N
          (canonicalPrefixPairBase b)))
        ((symProjToSector (unionSize p q (overlapSizeOfBase (canonicalPrefixPairBase b)) +
              (N - unionSize p q (overlapSizeOfBase (canonicalPrefixPairBase b))))).comp
          ((prefixTensorLift (H := H)
              (r := unionSize p q
                (overlapSizeOfBase (canonicalPrefixPairBase b)))
              (t := N - unionSize p q
                (overlapSizeOfBase (canonicalPrefixPairBase b)))
              (extendSymKernel (overlapFusionKernel C A Bop))).comp
            (SymSector ℂ H
              (unionSize p q (overlapSizeOfBase (canonicalPrefixPairBase b)) +
                (N - unionSize p q (overlapSizeOfBase (canonicalPrefixPairBase b))))).subtypeL)) := by
  classical
  let b₀ := canonicalPrefixPairBase b
  let s := overlapSizeOfBase b₀
  let hsP := overlapLeftBound b₀
  let hsQ := overlapRightBound b₀
  let r := p + (q - s)
  let hr : r ≤ N := pairPlacementBase_unionSize_le_N b₀
  let hU : b₀.1.2.card = r := by
    simpa [r, s, overlapSizeOfBase, unionSize] using b₀.2
  let h := Nat.add_sub_of_le hr
  let S := sourcePlacementOfSlots hr b₀.1.2 hU
  have hS : S = prefixInitialPlacementSubset r (N - r) := by
    apply Subtype.ext
    change castSlotSet (Nat.add_sub_of_le hr).symm b₀.1.2 =
      firstPositions (p := r) (q := N - r)
    rw [canonicalPrefixPairBase_slots]
    exact castPrefixSlots_eq_firstPositions hr
  have hkernel : averagedOverlapKernel hsP hsQ A Bop =
      overlapFusionKernel C A Bop :=
    averagedOverlapKernel_eq_overlapFusionKernel hsP hsQ C A Bop
  change arbitraryNSectorSubsetPlacement N r hr S
      (averagedOverlapKernel hsP hsQ A Bop) = _
  rw [hkernel, hS]
  unfold arbitraryNSectorSubsetPlacement actualSectorSubsetPlacement
  dsimp [r, unionSize, s]
  rw [subsetPlacement_prefixInitial_eq_firstPlacement]
  change castSymSectorOperator h
      ((symProjToSector (r + (N - r))).comp
        ((prefixTensorLift (H := H) (r := r) (t := N - r)
          (extendSymKernel (overlapFusionKernel C A Bop))).comp
          (SymSector ℂ H (r + (N - r))).subtypeL)) = _
  rfl

/-- If the aligned raw product has the ordered prefix-lift form, the frozen
local compression lemma identifies its global compression with the placed
averaged overlap kernel. -/
private theorem alignedRawOperator_eq_averagedPlacement
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (C : OverlapConfiguration p q
      (overlapSizeOfBase (canonicalPrefixPairBase b))
      (overlapLeftBound (canonicalPrefixPairBase b))
      (overlapRightBound (canonicalPrefixPairBase b)))
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q)
    (σ : Equiv.Perm (Fin N))
    (hraw : ambientRawPairOperator N p q hp hq
      (relabelActualPair hp hq σ
        (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C)) A Bop =
      castTensorOperator
        (Nat.add_sub_of_le (pairPlacementBase_unionSize_le_N
          (canonicalPrefixPairBase b)))
        (prefixTensorLift (H := H)
          (r := unionSize p q
            (overlapSizeOfBase (canonicalPrefixPairBase b)))
          (t := N - unionSize p q
            (overlapSizeOfBase (canonicalPrefixPairBase b)))
          ((subsetPlacement C.left A).comp (rightPlacement C Bop)))) :
    globallyCompressedRawPairTerm N p q hp hq
      (relabelActualPair hp hq σ
        (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C)) A Bop =
      averagedOverlapKernelPlacement N p q (canonicalPrefixPairBase b) A Bop := by
  let b₀ := canonicalPrefixPairBase b
  let r := p + (q - overlapSizeOfBase b₀)
  let hr : r ≤ N := pairPlacementBase_unionSize_le_N b₀
  let h := Nat.add_sub_of_le hr
  let T := (subsetPlacement C.left A).comp (rightPlacement C Bop)
  have hlocal := overlapFusionPrefixCompression_disappears
    (s := overlapSizeOfBase b₀) (t := N - r) C A Bop
  have hlocal' :
      (symProjToSector (r + (N - r))).comp
          ((prefixTensorLift (H := H) (r := r) (t := N - r)
            (extendSymKernel (overlapFusionKernel C A Bop))).comp
            (SymSector ℂ H (r + (N - r))).subtypeL) =
        (symProjToSector (r + (N - r))).comp
          ((prefixTensorLift (H := H) (r := r) (t := N - r) T).comp
            (SymSector ℂ H (r + (N - r))).subtypeL) := by
    simpa [r, T, unionSize] using hlocal
  have havg := averagedPrefixPlacement_eq_compressedFusion b C A Bop
  have hmatch : castSymSectorOperator h
      ((symProjToSector (r + (N - r))).comp
        ((prefixTensorLift (H := H) (r := r) (t := N - r) T).comp
          (SymSector ℂ H (r + (N - r))).subtypeL)) =
      averagedOverlapKernelPlacement N p q b₀ A Bop := by
    calc
      _ = castSymSectorOperator h
          ((symProjToSector (r + (N - r))).comp
            ((prefixTensorLift (H := H) (r := r) (t := N - r)
              (extendSymKernel (overlapFusionKernel C A Bop))).comp
              (SymSector ℂ H (r + (N - r))).subtypeL)) :=
        congrArg (castSymSectorOperator h) hlocal'.symm
      _ = _ := by
        exact congrArg (fun h' => castSymSectorOperator h'
          ((symProjToSector (r + (N - r))).comp
            ((prefixTensorLift (H := H) (r := r) (t := N - r)
              (extendSymKernel (overlapFusionKernel C A Bop))).comp
              (SymSector ℂ H (r + (N - r))).subtypeL)))
          (Subsingleton.elim h
            (Nat.add_sub_of_le (pairPlacementBase_unionSize_le_N b₀)))
      _ = _ := havg.symm
  change (symProjToSector N).comp
      ((ambientRawPairOperator N p q hp hq
        (relabelActualPair hp hq σ
          (canonicalToAmbientPair hp hq b₀ C)) A Bop).comp
        (SymSector ℂ H N).subtypeL) = _
  rw [hraw]
  calc
    _ = castSymSectorOperator h
        ((symProjToSector (r + (N - r))).comp
          ((prefixTensorLift (H := H) (r := r) (t := N - r) T).comp
            (SymSector ℂ H (r + (N - r))).subtypeL)) :=
      (castSymmetricCompression_eq h (prefixTensorLift T)).symm
    _ = _ := hmatch

/-- The compressed raw-term identity follows from the exact aligned ordered
transport gap.  The ambient permutation itself is absorbed by the frozen
global-compression covariance theorem. -/
theorem globallyCompressedCanonicalPrefixRawPairTerm_eq_averagedPlacement_of_alignedTransport
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q)
    (htransport : canonicalPrefixAlignedRawOperatorTransportGap hp hq b A Bop) :
    canonicalPrefixRawTermPlacementStatement hp hq b A Bop := by
  intro C
  obtain ⟨σ, hleft, hright⟩ :=
    exists_relabel_canonicalPrefix_slots hp hq b C
  have hright' :
      rightSlots hq (relabelActualPair hp hq σ
        (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C)) =
      (localRightSlots (overlapLeftBound (canonicalPrefixPairBase b))
        (overlapRightBound (canonicalPrefixPairBase b)) C).map
        (Fin.castLEEmb
          (pairPlacementBase_unionSize_le_N (canonicalPrefixPairBase b))) := by
    exact hright
  have hraw := htransport C σ hleft hright'
  have haligned := alignedRawOperator_eq_averagedPlacement hp hq b C A Bop σ hraw
  have hcov := globallyCompressedRawPairTerm_conjugate N p q hp hq σ
    (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C) A Bop
  calc
    globallyCompressedRawPairTerm N p q hp hq
        (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C) A Bop =
      globallyCompressedRawPairTerm N p q hp hq
        (relabelActualPair hp hq σ
          (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C)) A Bop := hcov.symm
    _ = averagedOverlapKernelPlacement N p q
        (canonicalPrefixPairBase b) A Bop := haligned

#print axioms QuantumNLS.PlacementFiberPrefixCompression.castPrefixSlots_eq_firstPositions
#print axioms QuantumNLS.PlacementFiberPrefixCompression.averagedPrefixPlacement_eq_compressedFusion
#print axioms QuantumNLS.PlacementFiberPrefixCompression.alignedRawOperator_eq_averagedPlacement
#print axioms QuantumNLS.PlacementFiberPrefixCompression.globallyCompressedCanonicalPrefixRawPairTerm_eq_averagedPlacement_of_alignedTransport

end QuantumNLS.PlacementFiberPrefixCompression

end

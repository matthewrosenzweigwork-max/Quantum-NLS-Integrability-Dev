/-
QuantumNLS.PlacementFiberPrefixBridge — identify one canonical raw pair
placement with placement of the averaged local overlap kernel.
-/
import QuantumNLS.PlacementFiberCanonicalPrefix

set_option maxHeartbeats 5000000

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberGrouping
  QuantumNLS.PlacementFiberBound QuantumNLS.PlacementFiberCanonicalPrefix

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private def localRightSet {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq) : Finset (Fin (p + (q - s))) :=
  C.right.1.map (overlapSlotEquiv hsp hsq).toEmbedding

theorem exists_relabel_canonicalPair_has_prefix_slots
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (C : OverlapConfiguration p q
      (overlapSizeOfBase (canonicalPrefixPairBase b))
      (overlapLeftBound (canonicalPrefixPairBase b))
      (overlapRightBound (canonicalPrefixPairBase b))) :
    ∃ σ : Equiv.Perm (Fin N),
      leftSlots hp
        (relabelActualPair hp hq σ
          (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C)) =
        C.left.1.map
          (Fin.castLEEmb (pairPlacementBase_unionSize_le_N
            (canonicalPrefixPairBase b))) ∧
      rightSlots hq
        (relabelActualPair hp hq σ
          (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C)) =
        (localRightSet (overlapLeftBound (canonicalPrefixPairBase b))
          (overlapRightBound (canonicalPrefixPairBase b)) C).map
          (Fin.castLEEmb (pairPlacementBase_unionSize_le_N
            (canonicalPrefixPairBase b))) := by
  classical
  let b₀ := canonicalPrefixPairBase b
  let r := p + (q - overlapSizeOfBase b₀)
  have hr : r ≤ N := by
    simpa [r, unionSize, overlapSizeOfBase] using
      pairPlacementBase_unionSize_le_N b₀
  have hU : b₀.1.2.card = r := by
    simpa [r, overlapSizeOfBase, unionSize] using b₀.2
  obtain ⟨σ, hσ⟩ := exists_unionSlotEmbedding_to_prefix_perm hr b₀.1.2 hU
  refine ⟨σ, ?_, ?_⟩
  · rw [leftSlots_relabelActualPair, canonicalToAmbientPair_leftSlots]
    change (pushUnionSlots b₀.1.2 hU C.left.1).map σ.toEmbedding = _
    dsimp [pushUnionSlots]
    rw [Finset.map_map]
    congr 1
    ext i
    exact congrArg Fin.val (hσ i)
  · rw [rightSlots_relabelActualPair, canonicalToAmbientPair_rightSlots]
    change (pushUnionSlots b₀.1.2 hU (localRightSet
      (overlapLeftBound b₀) (overlapRightBound b₀) C)).map σ.toEmbedding = _
    dsimp [pushUnionSlots]
    rw [Finset.map_map]
    congr 1
    ext i
    exact congrArg Fin.val (hσ i)

/-- The remaining operator slot-transport obligation after using the frozen
fact that the averaged local overlap kernel equals any concrete
`overlapFusionKernel` representative. -/
def canonicalPrefixRawTermPlacementOperatorGap
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) : Prop :=
  ∀ C : OverlapConfiguration p q
      (overlapSizeOfBase (canonicalPrefixPairBase b))
      (overlapLeftBound (canonicalPrefixPairBase b))
      (overlapRightBound (canonicalPrefixPairBase b)),
    globallyCompressedRawPairTerm N p q hp hq
      (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C) A Bop =
    arbitraryNSectorSubsetPlacement N
      (unionSize p q (overlapSizeOfBase (canonicalPrefixPairBase b)))
      (pairPlacementBase_unionSize_le_N (canonicalPrefixPairBase b))
      (sourcePlacementOfSlots
        (pairPlacementBase_unionSize_le_N (canonicalPrefixPairBase b))
        (canonicalPrefixPairBase b).1.2
        (by simpa [overlapSizeOfBase] using (canonicalPrefixPairBase b).2))
      (overlapFusionKernel C A Bop)

private theorem averagedPlacement_eq_fusionPlacement
    {N p q : ℕ} (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q)
    (C : OverlapConfiguration p q
      (overlapSizeOfBase (canonicalPrefixPairBase b))
      (overlapLeftBound (canonicalPrefixPairBase b))
      (overlapRightBound (canonicalPrefixPairBase b))) :
    averagedOverlapKernelPlacement N p q (canonicalPrefixPairBase b) A Bop =
      arbitraryNSectorSubsetPlacement N
        (unionSize p q (overlapSizeOfBase (canonicalPrefixPairBase b)))
        (pairPlacementBase_unionSize_le_N (canonicalPrefixPairBase b))
        (sourcePlacementOfSlots
          (pairPlacementBase_unionSize_le_N (canonicalPrefixPairBase b))
          (canonicalPrefixPairBase b).1.2
          (by simpa [overlapSizeOfBase] using (canonicalPrefixPairBase b).2))
        (overlapFusionKernel C A Bop) := by
  let b₀ := canonicalPrefixPairBase b
  let s := overlapSizeOfBase b₀
  let hsP := overlapLeftBound b₀
  let hsQ := overlapRightBound b₀
  let r := unionSize p q s
  have hr : r ≤ N := by
    dsimp [r, s]
    exact pairPlacementBase_unionSize_le_N b₀
  have hU : b₀.1.2.card = r := by
    simpa [r, s, overlapSizeOfBase] using b₀.2
  let S := sourcePlacementOfSlots hr b₀.1.2 hU
  change arbitraryNSectorSubsetPlacement N r hr S
      (averagedOverlapKernel hsP hsQ A Bop) =
    arbitraryNSectorSubsetPlacement N r hr S (overlapFusionKernel C A Bop)
  exact congrArg (arbitraryNSectorSubsetPlacement N r hr S)
    (averagedOverlapKernel_eq_overlapFusionKernel hsP hsQ C A Bop)

theorem canonicalPrefixRawTermPlacement_iff_operatorGap
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    canonicalPrefixRawTermPlacementStatement hp hq b A Bop ↔
      canonicalPrefixRawTermPlacementOperatorGap hp hq b A Bop := by
  classical
  constructor
  · intro h C
    rw [← averagedPlacement_eq_fusionPlacement b A Bop C]
    exact h C
  · intro h C
    rw [averagedPlacement_eq_fusionPlacement b A Bop C]
    exact h C

#print axioms QuantumNLS.PlacementFiberPrefixBridge.exists_relabel_canonicalPair_has_prefix_slots
#print axioms QuantumNLS.PlacementFiberPrefixBridge.canonicalPrefixRawTermPlacement_iff_operatorGap

end QuantumNLS.PlacementFiberPrefixBridge

end

/-
QuantumNLS.PlacementFiberPrefixSlotTransport — exact slot transport from
canonical union coordinates to the ambient prefix.

This module extends the frozen prefix lift read-only.
-/
import QuantumNLS.PlacementFiberPrefixLift

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

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixSlotTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private def localRightSlots {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (C : OverlapConfiguration p q s hsp hsq) : Finset (Fin (p + (q - s))) :=
  C.right.1.map (overlapSlotEquiv hsp hsq).toEmbedding

/-- The canonical pair's actual left slots are the image of its local left
subset under the union enumeration.  This records the enumeration map itself;
it does not identify that map with the ordered prefix embedding. -/
theorem canonicalPrefix_leftSlots_viaUnionEnumeration
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (C : OverlapConfiguration p q
      (overlapSizeOfBase (canonicalPrefixPairBase b))
      (overlapLeftBound (canonicalPrefixPairBase b))
      (overlapRightBound (canonicalPrefixPairBase b))) :
    leftSlots hp (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C) =
      C.left.1.map (unionSlotEmbedding (canonicalPrefixPairBase b).1.2
        (by simpa [overlapSizeOfBase, unionSize] using
          (canonicalPrefixPairBase b).2)) := by
  rw [canonicalToAmbientPair_leftSlots]
  rfl

/-- The canonical pair's actual right slots use the same union enumeration,
after the frozen cast from the q-placement coordinates to the common local
union coordinates. -/
theorem canonicalPrefix_rightSlots_viaUnionEnumeration
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (C : OverlapConfiguration p q
      (overlapSizeOfBase (canonicalPrefixPairBase b))
      (overlapLeftBound (canonicalPrefixPairBase b))
      (overlapRightBound (canonicalPrefixPairBase b))) :
    rightSlots hq (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C) =
      (localRightSlots (overlapLeftBound (canonicalPrefixPairBase b))
        (overlapRightBound (canonicalPrefixPairBase b)) C).map
        (unionSlotEmbedding (canonicalPrefixPairBase b).1.2
          (by simpa [overlapSizeOfBase, unionSize] using
            (canonicalPrefixPairBase b).2)) := by
  rw [canonicalToAmbientPair_rightSlots]
  rfl

/-- The frozen bridge proves that an ambient permutation can align both
slot images with the ordered prefix.  The direct raw-operator equation still
needs the corresponding ordered transport, which is intentionally left as
the exact gap in `PlacementFiberPrefixLift`. -/
theorem exists_relabel_canonicalPrefix_slots
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (C : OverlapConfiguration p q
      (overlapSizeOfBase (canonicalPrefixPairBase b))
      (overlapLeftBound (canonicalPrefixPairBase b))
      (overlapRightBound (canonicalPrefixPairBase b))) :
    ∃ σ : Equiv.Perm (Fin N),
      leftSlots hp (relabelActualPair hp hq σ
        (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C)) =
        C.left.1.map (Fin.castLEEmb
          (pairPlacementBase_unionSize_le_N (canonicalPrefixPairBase b))) ∧
      rightSlots hq (relabelActualPair hp hq σ
        (canonicalToAmbientPair hp hq (canonicalPrefixPairBase b) C)) =
        (localRightSlots (overlapLeftBound (canonicalPrefixPairBase b))
          (overlapRightBound (canonicalPrefixPairBase b)) C).map
          (Fin.castLEEmb
            (pairPlacementBase_unionSize_le_N (canonicalPrefixPairBase b))) :=
  PlacementFiberPrefixBridge.exists_relabel_canonicalPair_has_prefix_slots
    hp hq b C

#print axioms QuantumNLS.PlacementFiberPrefixSlotTransport.canonicalPrefix_leftSlots_viaUnionEnumeration
#print axioms QuantumNLS.PlacementFiberPrefixSlotTransport.canonicalPrefix_rightSlots_viaUnionEnumeration
#print axioms QuantumNLS.PlacementFiberPrefixSlotTransport.exists_relabel_canonicalPrefix_slots

end QuantumNLS.PlacementFiberPrefixSlotTransport

end

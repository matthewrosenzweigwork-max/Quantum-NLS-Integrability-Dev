/-
QuantumNLS.PlacementFiberPrefixLift — ordered local product transport for
the canonical-prefix LOCAL-011 comparison.

This module imports the frozen prefix bridge read-only.  It records the exact
ordered prefix-lift gap and proves the tensor-product algebra and local
compression step that follow once slot compatibility is established.
-/
import QuantumNLS.PlacementFiberPrefixBridge

set_option maxHeartbeats 5000000

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberGrouping
  QuantumNLS.PlacementFiberBound QuantumNLS.PlacementFiberCanonicalPrefix
  QuantumNLS.PlacementFiberPrefixBridge

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixLift

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Exact raw-operator form of the remaining subset-placement/prefix-lift
compatibility.  It compares the actual ambient pair contribution, in its
source order, with the lift of the ordered local product on the union slots.
This proposition is a gap statement, not an assumed theorem. -/
def canonicalPrefixOrderedProductPrefixLiftGap
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) : Prop :=
  ∀ C : OverlapConfiguration p q
      (overlapSizeOfBase (canonicalPrefixPairBase b))
      (overlapLeftBound (canonicalPrefixPairBase b))
      (overlapRightBound (canonicalPrefixPairBase b)),
    let b₀ := canonicalPrefixPairBase b
    let r := unionSize p q (overlapSizeOfBase b₀)
    let hr : r ≤ N := pairPlacementBase_unionSize_le_N b₀
    ambientRawPairOperator N p q hp hq
        (canonicalToAmbientPair hp hq b₀ C) A Bop =
      castTensorOperator (Nat.add_sub_of_le hr)
        (prefixTensorLift (H := H) (r := r) (t := N - r)
          ((subsetPlacement C.left A).comp (rightPlacement C Bop)))

omit [CompleteSpace H] in
/-- Prefix lifting respects the composition order of the local pair. -/
theorem prefixTensorLift_localOrderedProduct
    {r t : ℕ}
    (X Y : HilbertTensorPower ℂ H r →L[ℂ] HilbertTensorPower ℂ H r) :
    prefixTensorLift (H := H) (r := r) (t := t) (X.comp Y) =
      (prefixTensorLift (H := H) (r := r) (t := t) X).comp
        (prefixTensorLift (H := H) (r := r) (t := t) Y) := by
  exact (prefixTensorLift_comp X Y).symm

omit [CompleteSpace H] in
/-- After the local overlap kernel is prefix-lifted, its local symmetric
compression disappears under global symmetric compression.  This is the
frozen compression lemma specialized to an arbitrary ordered local operator.
-/
theorem prefixTensorLift_localCompression_disappears
    {r t : ℕ}
    (T : HilbertTensorPower ℂ H r →L[ℂ] HilbertTensorPower ℂ H r) :
    (symProjToSector (r + t)).comp
        ((prefixTensorLift (H := H) (r := r) (t := t)
          (extendSymKernel ((symProjToSector r).comp
            (T.comp (SymSector ℂ H r).subtypeL)))).comp
          (SymSector ℂ H (r + t)).subtypeL) =
      (symProjToSector (r + t)).comp
        ((prefixTensorLift (H := H) (r := r) (t := t) T).comp
          (SymSector ℂ H (r + t)).subtypeL) := by
  exact localSymmetricCompression_disappears_after_globalCompression T

/-- The preceding compression step for the concrete ordered overlap product
on one canonical local configuration. -/
theorem overlapFusionPrefixCompression_disappears
    {p q s t : ℕ} {hsp : s ≤ p} {hsq : s ≤ q}
    (C : OverlapConfiguration p q s hsp hsq)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (symProjToSector (p + (q - s) + t)).comp
        ((prefixTensorLift (H := H) (r := p + (q - s)) (t := t)
          (extendSymKernel (overlapFusionKernel C A Bop))).comp
          (SymSector ℂ H (p + (q - s) + t)).subtypeL) =
      (symProjToSector (p + (q - s) + t)).comp
        ((prefixTensorLift (H := H) (r := p + (q - s)) (t := t)
          ((subsetPlacement C.left A).comp (rightPlacement C Bop))).comp
          (SymSector ℂ H (p + (q - s) + t)).subtypeL) := by
  exact prefixTensorLift_localCompression_disappears
    ((subsetPlacement C.left A).comp (rightPlacement C Bop))

#print axioms QuantumNLS.PlacementFiberPrefixLift.prefixTensorLift_localOrderedProduct
#print axioms QuantumNLS.PlacementFiberPrefixLift.prefixTensorLift_localCompression_disappears
#print axioms QuantumNLS.PlacementFiberPrefixLift.overlapFusionPrefixCompression_disappears

end QuantumNLS.PlacementFiberPrefixLift

end

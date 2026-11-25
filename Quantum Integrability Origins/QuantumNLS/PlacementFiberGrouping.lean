/-
QuantumNLS.PlacementFiberGrouping — the source-normalized grouping of the
full ambient product by union and overlap fibers.

The central comparison with `averagedOverlapKernel` is kept separate: this
file records the exact finite grouping with the ambient fiber averages still
visible, and preserves the full-sum-only rule for the middle projection.
-/
import QuantumNLS.PlacementFiberOperator

set_option maxHeartbeats 5000000

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator

noncomputable section

namespace QuantumNLS.PlacementFiberGrouping

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The coefficient of one union-overlap key in the literal source
normalization: the hypergeometric overlap probability divided by the number
of ambient unions of that size. -/
def sourceNormalizedAmbientFiberTerm
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  (((overlapCoefficient N p q (overlapSizeOfBase b) : ℝ) : ℂ) *
      (Nat.choose N (unionSize p q (overlapSizeOfBase b)) : ℂ)⁻¹) •
    globallyCompressedAmbientFiberContribution N p q hp hq b A Bop

private theorem ambientRawPairSum_eq_product
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (∑ z : ActualPairPlacement N p q,
      ambientRawPairOperator N p q hp hq z A Bop) =
      (rawSubsetPlacementSum N p hp A).comp
        (rawSubsetPlacementSum N q hq Bop) := by
  classical
  ext x
  let L := fun S : PlacementSubset p (N - p) =>
    castTensorOperator (Nat.add_sub_of_le hp) (subsetPlacement S A)
  let R := fun T : PlacementSubset q (N - q) =>
    castTensorOperator (Nat.add_sub_of_le hq) (subsetPlacement T Bop)
  calc
    (∑ z : ActualPairPlacement N p q, (L z.1).comp (R z.2)) x =
        ∑ S : PlacementSubset p (N - p),
          ∑ T : PlacementSubset q (N - q), (L S).comp (R T) x := by
      simpa [L, R, ActualPairPlacement] using
        (Fintype.sum_prod_type'
          (fun S T => (L S).comp (R T) x))
    _ = ((∑ S : PlacementSubset p (N - p), L S).comp
          (∑ T : PlacementSubset q (N - q), R T)) x := by
      simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum]
      conv_rhs => rw [Finset.sum_comm]
    _ = _ := rfl

private theorem ambientFiberSum_eq_globalRawCompression
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (∑ z : ActualPairPlacement N p q,
      globallyCompressedRawPairTerm N p q hp hq z A Bop) =
      (symProjToSector N).comp
        ((rawSubsetPlacementSum N p hp A).comp
          ((rawSubsetPlacementSum N q hq Bop).comp
            (SymSector ℂ H N).subtypeL)) := by
  classical
  unfold globallyCompressedRawPairTerm
  calc
    _ = (symProjToSector N).comp
        (((∑ z : ActualPairPlacement N p q,
          ambientRawPairOperator N p q hp hq z A Bop)).comp
          (SymSector ℂ H N).subtypeL) := by
      ext x
      simp [ContinuousLinearMap.comp_apply, map_sum]
    _ = _ := by
      rw [ambientRawPairSum_eq_product, ContinuousLinearMap.comp_assoc]

private theorem ambientFiberSum_eq_sectorPairSum
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (∑ z : ActualPairPlacement N p q,
      globallyCompressedRawPairTerm N p q hp hq z A Bop) =
      ∑ S : PlacementSubset p (N - p),
        ∑ T : PlacementSubset q (N - q),
          (arbitraryNSectorSubsetPlacement N p hp S A).comp
            (arbitraryNSectorSubsetPlacement N q hq T Bop) := by
  rw [ambientFiberSum_eq_globalRawCompression]
  exact (actualPairSectorSum_eq_globalRawCompression N p q hp hq A Bop).symm

private theorem ambientFiberContribution_card_mul
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (∑ z : pairUnionFiber hp hq b,
      globallyCompressedRawPairTerm N p q hp hq z.1 A Bop) =
      (Fintype.card (pairUnionFiber hp hq b) : ℂ) •
        globallyCompressedAmbientFiberContribution N p q hp hq b A Bop := by
  classical
  let s := overlapSizeOfBase b
  let hsP := overlapLeftBound b
  let hsQ := overlapRightBound b
  let e := ambientFiberOverlapEquiv hp hq b
  have hconfig : Fintype.card (OverlapConfiguration p q s hsP hsQ) =
      Nat.choose (unionSize p q s) p * Nat.choose p s := by
    simpa [s, unionSize] using card_overlapConfiguration hsP hsQ
  have hpos : 0 < Fintype.card (OverlapConfiguration p q s hsP hsQ) := by
    rw [hconfig]
    exact Nat.mul_pos
      (Nat.choose_pos (show p ≤ unionSize p q s by dsimp [unionSize]; omega))
      (Nat.choose_pos hsP)
  have hcard : (Fintype.card (pairUnionFiber hp hq b) : ℂ) ≠ 0 := by
    rw [Fintype.card_congr e]
    exact_mod_cast (Nat.ne_of_gt hpos)
  change (∑ z : pairUnionFiber hp hq b,
      globallyCompressedRawPairTerm N p q hp hq z.1 A Bop) = _
  rw [globallyCompressedAmbientFiberContribution]
  change (∑ z : pairUnionFiber hp hq b,
      globallyCompressedRawPairTerm N p q hp hq z.1 A Bop) =
    (Fintype.card (pairUnionFiber hp hq b) : ℂ) •
      ((Fintype.card (pairUnionFiber hp hq b) : ℂ)⁻¹ •
        ∑ z : pairUnionFiber hp hq b,
          globallyCompressedRawPairTerm N p q hp hq z.1 A Bop)
  rw [smul_smul]
  simp [hcard]

private theorem sourceFiberWeight_eq
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q) :
    ((Nat.choose N p : ℂ)⁻¹ * (Nat.choose N q : ℂ)⁻¹) *
        (Fintype.card (pairUnionFiber hp hq b) : ℂ) =
      (((overlapCoefficient N p q (overlapSizeOfBase b) : ℝ) : ℂ) *
        (Nat.choose N (unionSize p q (overlapSizeOfBase b)) : ℂ)⁻¹) := by
  let s := overlapSizeOfBase b
  let hsP := overlapLeftBound b
  let hsQ := overlapRightBound b
  let hr := pairPlacementBase_unionSize_le_N b
  let e := ambientFiberOverlapEquiv hp hq b
  have hnorm := overlapFiber_pairNormalization hsP hsQ hr
  have hcardCfg : Fintype.card (OverlapConfiguration p q s hsP hsQ) =
      Nat.choose (unionSize p q s) p * Nat.choose p s := by
    simpa [s, unionSize] using card_overlapConfiguration hsP hsQ
  have hpos : 0 < Fintype.card (OverlapConfiguration p q s hsP hsQ) := by
    rw [hcardCfg]
    exact Nat.mul_pos
      (Nat.choose_pos (show p ≤ unionSize p q s by dsimp [unionSize]; omega))
      (Nat.choose_pos hsP)
  have hcard : (Fintype.card (pairUnionFiber hp hq b) : ℝ) =
      Fintype.card (OverlapConfiguration p q s hsP hsQ) := by
    exact_mod_cast (Fintype.card_congr e)
  have hcardC : (Fintype.card (pairUnionFiber hp hq b) : ℂ) =
      Fintype.card (OverlapConfiguration p q s hsP hsQ) := by
    exact_mod_cast hcard
  have hcard_ne : (Fintype.card (OverlapConfiguration p q s hsP hsQ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  have hnp : (Nat.choose N p : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hp
  have hnq : (Nat.choose N q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hq
  have hnr : (Nat.choose N (unionSize p q s) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (pairPlacementBase_unionSize_le_N b)
  have hmul :
      overlapCoefficient N p q s *
          (Nat.choose N (unionSize p q s) : ℝ)⁻¹ =
        ((Nat.choose N p : ℝ)⁻¹ * (Nat.choose N q : ℝ)⁻¹) *
          Fintype.card (OverlapConfiguration p q s hsP hsQ) := by
    calc
      _ = (overlapCoefficient N p q s *
            (Fintype.card (OverlapConfiguration p q s hsP hsQ) : ℝ)⁻¹ *
            (Nat.choose N (unionSize p q s) : ℝ)⁻¹) *
            Fintype.card (OverlapConfiguration p q s hsP hsQ) := by
              field_simp [hcard_ne]
      _ = _ := by
        rw [hnorm]
        field_simp [hnp, hnq]
  have hmulC := congrArg (fun x : ℝ => (x : ℂ)) hmul
  rw [hcardC]
  simpa [s, mul_assoc] using hmulC.symm

/-- Exact product grouping by actual union and overlap.  The middle
symmetric projection has been removed only after the complete pair sum, and
the remaining ambient fiber average retains the printed source normalization.
-/
theorem genericU_product_eq_sourceNormalizedAmbientFiberGrouping
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (genericU_N_r N p hp A).comp (genericU_N_r N q hq Bop) =
      ∑ b : PairPlacementBase N p q,
        sourceNormalizedAmbientFiberTerm N p q hp hq b A Bop := by
  classical
  let c : ℂ := (Nat.choose N p : ℂ)⁻¹ * (Nat.choose N q : ℂ)⁻¹
  rw [arbitraryN_product_eq_actualPairPlacementSum]
  rw [(ambientFiberSum_eq_sectorPairSum N p q hp hq A Bop).symm]
  change c •
      (∑ z : ActualPairPlacement N p q,
        globallyCompressedRawPairTerm N p q hp hq z A Bop) = _
  rw [sum_pairPlacement_eq_sum_unionFibers hp hq
    (fun z => globallyCompressedRawPairTerm N p q hp hq z A Bop)]
  rw [Fintype.sum_sigma]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [ambientFiberContribution_card_mul]
  rw [smul_smul]
  change (((Nat.choose N p : ℂ)⁻¹ * (Nat.choose N q : ℂ)⁻¹) *
      Fintype.card (pairUnionFiber hp hq b)) •
      globallyCompressedAmbientFiberContribution N p q hp hq b A Bop = _
  rw [sourceFiberWeight_eq]
  rfl

#print axioms QuantumNLS.PlacementFiberGrouping.sourceNormalizedAmbientFiberTerm
#print axioms QuantumNLS.PlacementFiberGrouping.genericU_product_eq_sourceNormalizedAmbientFiberGrouping

end QuantumNLS.PlacementFiberGrouping

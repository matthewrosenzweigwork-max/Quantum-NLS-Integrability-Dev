/-
QuantumNLS.PlacementGrouping — full pair-sum identities for LOCAL-011.

The middle symmetric projection is removed only after summing the actual
placement pairs.  The local overlap average is the frozen, N-independent
kernel from PlacementProduct.
-/
import QuantumNLS.PlacementCovariance

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance

noncomputable section

namespace QuantumNLS.PlacementGrouping

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- A tensor operator that preserves the symmetric sector still does so after
the canonical equality transport between tensor-power indices. -/
theorem castTensorOperator_preserves_sector {m n : ℕ} (h : m = n)
    (T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m)
    (hT : ∀ x : SymSector ℂ H m, T x.1 ∈ SymSector ℂ H m)
    (x : SymSector ℂ H n) :
    castTensorOperator h T x.1 ∈ SymSector ℂ H n := by
  cases h
  exact hT x

omit [CompleteSpace H] in
/-- Restricting to the symmetric sector commutes with a tensor-index cast. -/
theorem castSymSectorOperator_restriction_eq {m n : ℕ} (h : m = n)
    (T : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m)
    (hT : ∀ x : SymSector ℂ H m, T x.1 ∈ SymSector ℂ H m) :
    castSymSectorOperator h
        ((T.comp (SymSector ℂ H m).subtypeL).codRestrict (SymSector ℂ H m) hT) =
      ((castTensorOperator h T).comp (SymSector ℂ H n).subtypeL).codRestrict
        (SymSector ℂ H n) (castTensorOperator_preserves_sector h T hT) := by
  cases h
  rfl

/-- The literal full-tensor subset average, transported to the requested
particle count. -/
def rawSubsetAverage (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) :
    HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N :=
  castTensorOperator (Nat.add_sub_of_le hr)
    (subsetPlacementAverage (q := N - r) A)

/-- A single uncompressed placement, transported to the literal N tensor
power. -/
def rawSubsetPlacement (N r : ℕ) (hr : r ≤ N)
    (S : PlacementSubset r (N - r)) (A : BoundedSymmetricKernel H r) :
    HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N :=
  castTensorOperator (Nat.add_sub_of_le hr) (subsetPlacement S A)

/-- The actual uncompressed sum over all r-subsets of the N slots. -/
def rawSubsetPlacementSum (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) :
    HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N :=
  ∑ S : PlacementSubset r (N - r), rawSubsetPlacement N r hr S A

omit [CompleteSpace H] in
private theorem castTensorOperator_smul_sum {m n : ℕ} (h : m = n)
    {ι : Type*} [Fintype ι] (c : ℂ)
    (F : ι → HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) :
    castTensorOperator h (c • ∑ i, F i) =
      c • ∑ i, castTensorOperator h (F i) := by
  cases h
  rfl

/-- The full-tensor average has exactly the source reciprocal-binomial
normalization over the actual placements. -/
theorem rawSubsetAverage_eq_rawSubsetPlacementSum
    (N r : ℕ) (hr : r ≤ N) (A : BoundedSymmetricKernel H r) :
    rawSubsetAverage N r hr A =
      ((Nat.choose N r : ℂ)⁻¹) • rawSubsetPlacementSum N r hr A := by
  unfold rawSubsetAverage rawSubsetPlacementSum rawSubsetPlacement
  unfold subsetPlacementAverage
  rw [castTensorOperator_smul_sum]
  have hchoose : Nat.choose (r + (N - r)) r = Nat.choose N r :=
    congrArg (fun n => Nat.choose n r) (Nat.add_sub_of_le hr)
  rw [hchoose]

/-- The raw subset average preserves the N-particle symmetric sector. -/
theorem rawSubsetAverage_apply_mem (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) (x : SymSector ℂ H N) :
    rawSubsetAverage N r hr A x.1 ∈ SymSector ℂ H N := by
  exact castTensorOperator_preserves_sector (Nat.add_sub_of_le hr)
    (subsetPlacementAverage (q := N - r) A)
    (subsetPlacementAverage_apply_mem A) x

/-- Restriction of the literal full-tensor average to the symmetric sector. -/
def rawSubsetAverageOnSector (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  ((rawSubsetAverage N r hr A).comp (SymSector ℂ H N).subtypeL).codRestrict
    (SymSector ℂ H N) (rawSubsetAverage_apply_mem N r hr A)

/-- The source operator is the restriction of the full-tensor subset average. -/
theorem genericU_eq_rawSubsetAverageOnSector
    (N r : ℕ) (hr : r ≤ N) (A : BoundedSymmetricKernel H r) :
    genericU_N_r N r hr A = rawSubsetAverageOnSector N r hr A := by
  rw [genericU_N_r_eq_subsetPlacementAverage]
  unfold genericSubsetPlacementAverage rawSubsetAverageOnSector rawSubsetAverage
  exact castSymSectorOperator_restriction_eq (Nat.add_sub_of_le hr)
    (subsetPlacementAverage (q := N - r) A)
    (subsetPlacementAverage_apply_mem A)

omit [CompleteSpace H] in
/-- On the symmetric sector, composing two sector-preserving operators is
the single symmetric compression of their full-tensor product. -/
theorem restriction_comp_eq_singleCompression {N : ℕ}
    (T U : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N)
    (hT : ∀ x : SymSector ℂ H N, T x.1 ∈ SymSector ℂ H N)
    (hU : ∀ x : SymSector ℂ H N, U x.1 ∈ SymSector ℂ H N) :
    (((T.comp (SymSector ℂ H N).subtypeL).codRestrict
        (SymSector ℂ H N) hT).comp
      ((U.comp (SymSector ℂ H N).subtypeL).codRestrict
        (SymSector ℂ H N) hU)) =
      (symProjToSector N).comp
        ((T.comp U).comp (SymSector ℂ H N).subtypeL) := by
  ext x
  change T (U x.1) = symProj ℂ H N (T (U x.1))
  symm
  rw [symProj_eq_starProjection]
  exact Submodule.starProjection_eq_self_iff.mpr (hT ⟨U x.1, hU x⟩)

/-- The arbitrary-N pair sum loses its intermediate symmetric projection after
the full sum is formed.  The right side is the compression of the actual
uncompressed pair sum. -/
theorem actualPairSum_eq_singleCompression
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    (∑ S : PlacementSubset p (N - p),
      ∑ T : PlacementSubset q (N - q),
        (arbitraryNSectorSubsetPlacement N p hp S A).comp
          (arbitraryNSectorSubsetPlacement N q hq T B)) =
      (symProjToSector N).comp
        ((rawSubsetPlacementSum N p hp A).comp
          ((rawSubsetPlacementSum N q hq B).comp
            (SymSector ℂ H N).subtypeL)) := by
  let c : ℂ := (Nat.choose N p : ℂ)⁻¹ * (Nat.choose N q : ℂ)⁻¹
  have hproduct := arbitraryN_product_eq_actualPairPlacementSum
    (H := H) N p q hp hq A B
  have hsector := restriction_comp_eq_singleCompression
    (N := N) (rawSubsetAverage N p hp A) (rawSubsetAverage N q hq B)
    (rawSubsetAverage_apply_mem N p hp A) (rawSubsetAverage_apply_mem N q hq B)
  have hsource :
      (genericU_N_r N p hp A).comp (genericU_N_r N q hq B) =
        (rawSubsetAverageOnSector N p hp A).comp
          (rawSubsetAverageOnSector N q hq B) := by
    rw [genericU_eq_rawSubsetAverageOnSector, genericU_eq_rawSubsetAverageOnSector]
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero
    · exact inv_ne_zero (by
        exact_mod_cast (Nat.choose_ne_zero hp))
    · exact inv_ne_zero (by
        exact_mod_cast (Nat.choose_ne_zero hq))
  have hscaled :
      c • (∑ S : PlacementSubset p (N - p),
        ∑ T : PlacementSubset q (N - q),
          (arbitraryNSectorSubsetPlacement N p hp S A).comp
            (arbitraryNSectorSubsetPlacement N q hq T B)) =
      c • ((symProjToSector N).comp
        ((rawSubsetPlacementSum N p hp A).comp
          ((rawSubsetPlacementSum N q hq B).comp
            (SymSector ℂ H N).subtypeL))) := by
    calc
      _ = (genericU_N_r N p hp A).comp (genericU_N_r N q hq B) := by
            simpa [c] using hproduct.symm
      _ = (symProjToSector N).comp
          ((rawSubsetAverage N p hp A).comp
            ((rawSubsetAverage N q hq B).comp
              (SymSector ℂ H N).subtypeL)) := hsource.trans hsector
      _ = _ := by
            rw [rawSubsetAverage_eq_rawSubsetPlacementSum,
              rawSubsetAverage_eq_rawSubsetPlacementSum]
            ext x
            simp [c, rawSubsetPlacementSum, ContinuousLinearMap.comp_apply,
              map_smul, smul_apply, Finset.smul_sum, smul_smul, mul_comm]
  have hcancel := congrArg (fun z => c⁻¹ • z) hscaled
  simpa [smul_smul, hc] using hcancel

/-- If the required union has more than N slots, its source overlap
coefficient is zero.  This is the impossible-union case in the grouping. -/
theorem overlapCoefficient_eq_zero_of_unionSize_gt
    {N p q s : ℕ} (hp : p ≤ N) (hsq : s ≤ q)
    (hlarge : N < unionSize p q s) :
    overlapCoefficient N p q s = 0 := by
  have hrest : N - p < q - s := by
    dsimp [unionSize] at hlarge
    omega
  unfold overlapCoefficient
  rw [ite_eq_left hsq]
  have hchoose : Nat.choose (N - p) (q - s) = 0 :=
    Nat.choose_eq_zero_of_lt hrest
  simp [hchoose]

end QuantumNLS.PlacementGrouping

#print axioms QuantumNLS.PlacementGrouping.rawSubsetAverage_eq_rawSubsetPlacementSum
#print axioms QuantumNLS.PlacementGrouping.restriction_comp_eq_singleCompression
#print axioms QuantumNLS.PlacementGrouping.actualPairSum_eq_singleCompression
#print axioms QuantumNLS.PlacementGrouping.overlapCoefficient_eq_zero_of_unionSize_gt

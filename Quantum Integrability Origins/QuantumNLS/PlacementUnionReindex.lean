/-
QuantumNLS.PlacementUnionReindex — reindex the actual pair placements by
their union and overlap size for LOCAL-011.

This module starts from the frozen actual pair-placement sum and constructs
the finite index equivalence needed to identify its union fibers with the
frozen averaged overlap kernel.
-/
import QuantumNLS.PlacementGrouping

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping

noncomputable section

namespace QuantumNLS.PlacementUnionReindex

/-- The actual pair of independently chosen source placements in `N` slots. -/
abbrev ActualPairPlacement (N p q : ℕ) :=
  PlacementSubset p (N - p) × PlacementSubset q (N - q)

/-- Cast a finite set along an equality of slot counts. -/
def castSlotSet {m n : ℕ} (h : m = n) (S : Finset (Fin m)) : Finset (Fin n) :=
  S.map (Equiv.cast (congrArg Fin h)).toEmbedding

/-- The source left placement viewed in the literal `Fin N` slot set. -/
def leftSlots {N p q : ℕ} (hp : p ≤ N) (z : ActualPairPlacement N p q) :
    Finset (Fin N) :=
  castSlotSet (Nat.add_sub_of_le hp) z.1.1

/-- The source right placement viewed in the literal `Fin N` slot set. -/
def rightSlots {N p q : ℕ} (hq : q ≤ N) (z : ActualPairPlacement N p q) :
    Finset (Fin N) :=
  castSlotSet (Nat.add_sub_of_le hq) z.2.1

/-- An admissible union/overlap key. The union is a subset of the literal
`Fin N` slot set, and its size is fixed by the overlap. -/
abbrev PairPlacementBase (N p q : ℕ) :=
  {b : ({s : ℕ // s ≤ min p q} × Finset (Fin N)) //
    b.2.card = unionSize p q b.1.1}

noncomputable instance pairPlacementBaseFintype (N p q : ℕ) :
    Fintype (PairPlacementBase N p q) := by
  classical
  exact Fintype.ofFinite _

/-- A union/overlap key can exist only when its source union fits in `N`.
Thus the reindexed sum has no fibers for impossible union sizes. -/
theorem pairPlacementBase_unionSize_le_N
    {N p q : ℕ} (b : PairPlacementBase N p q) :
    unionSize p q b.1.1 ≤ N := by
  rw [← b.2]
  have h := Finset.card_le_card (Finset.subset_univ b.1.2)
  simpa using h

/-- The union/overlap key of one actual source pair. -/
def pairPlacementKey {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (z : ActualPairPlacement N p q) : PairPlacementBase N p q := by
  let S := leftSlots hp z
  let T := rightSlots hq z
  let s := (S ∩ T).card
  have hS : S.card = p := by simpa [S, leftSlots, castSlotSet] using z.1.2
  have hT : T.card = q := by simpa [T, rightSlots, castSlotSet] using z.2.2
  have hsP : s ≤ p := by
    calc
      s = (S ∩ T).card := rfl
      _ ≤ S.card := Finset.card_le_card Finset.inter_subset_left
      _ = p := hS
  have hsQ : s ≤ q := by
    calc
      s = (T ∩ S).card := by rw [Finset.inter_comm]
      _ ≤ T.card := Finset.card_le_card Finset.inter_subset_left
      _ = q := hT
  have hUnion : (S ∪ T).card = unionSize p q s := by
    rw [unionSize]
    have h := Finset.card_inter_add_card_union S T
    rw [hS, hT] at h
    change (S ∩ T).card + (S ∪ T).card = p + q at h
    rw [show (S ∩ T).card = s from rfl] at h
    omega
  exact ⟨(⟨s, le_min hsP hsQ⟩, S ∪ T), hUnion⟩

/-- Pair indices in a fixed actual union and overlap fiber. -/
def pairUnionFiber {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (b : PairPlacementBase N p q) :=
  {z : ActualPairPlacement N p q // pairPlacementKey hp hq z = b}

noncomputable instance pairUnionFiberFintype {N p q : ℕ} (hp : p ≤ N)
    (hq : q ≤ N) (b : PairPlacementBase N p q) :
    Fintype (pairUnionFiber hp hq b) := by
  classical
  let f : pairUnionFiber hp hq b → ActualPairPlacement N p q := Subtype.val
  have hf : Function.Injective f := fun x y h => Subtype.ext h
  letI : Finite (pairUnionFiber hp hq b) := Finite.of_injective f hf
  exact Fintype.ofFinite _

/-- Reindex all actual pairs first by their overlap size and then by their
actual union subset.  The fiber retains the original pair data, so this is a
literal finite-index equivalence before any operator transport is applied. -/
noncomputable def pairPlacementUnionEquiv (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) :
    ActualPairPlacement N p q ≃
      Σ b : PairPlacementBase N p q, pairUnionFiber hp hq b :=
  (Equiv.sigmaFiberEquiv (pairPlacementKey hp hq)).symm

/-- The source pair sum is exactly the sum over actual union/overlap fibers.
This is only a finite-index reindexing; the operator identification of each
fiber with the frozen local average is proved separately below. -/
theorem sum_pairPlacement_eq_sum_unionFibers
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    {M : Type*} [AddCommMonoid M]
    (F : ActualPairPlacement N p q → M) :
    (∑ z : ActualPairPlacement N p q, F z) =
      ∑ y : Σ b : PairPlacementBase N p q, pairUnionFiber hp hq b,
        F y.2.1 := by
  classical
  exact Equiv.sum_comp (pairPlacementUnionEquiv N p q hp hq)
    (fun y => F y.2.1)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The operator-valued source pair sum, in its literal `Fin N` union fibers.
The summands are still the original actual placements; the separate local
kernel identification is the remaining step toward LOCAL-011. -/
theorem actualPairOperatorSum_eq_unionFibers
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    (∑ z : ActualPairPlacement N p q,
      (arbitraryNSectorSubsetPlacement N p hp z.1 A).comp
        (arbitraryNSectorSubsetPlacement N q hq z.2 B)) =
      ∑ y : Σ b : PairPlacementBase N p q, pairUnionFiber hp hq b,
        (arbitraryNSectorSubsetPlacement N p hp y.2.1.1 A).comp
          (arbitraryNSectorSubsetPlacement N q hq y.2.1.2 B) := by
  let F := fun z : ActualPairPlacement N p q =>
    (arbitraryNSectorSubsetPlacement N p hp z.1 A).comp
      (arbitraryNSectorSubsetPlacement N q hq z.2 B)
  simpa [F] using sum_pairPlacement_eq_sum_unionFibers hp hq F

/-- The source product expansion with its two binomial normalization factors,
now indexed by actual union/overlap fibers. -/
theorem genericU_product_eq_unionFiberSum
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    (genericU_N_r N p hp A).comp (genericU_N_r N q hq B) =
      (((Nat.choose N p : ℂ)⁻¹) * ((Nat.choose N q : ℂ)⁻¹)) •
        ∑ y : Σ b : PairPlacementBase N p q, pairUnionFiber hp hq b,
          (arbitraryNSectorSubsetPlacement N p hp y.2.1.1 A).comp
            (arbitraryNSectorSubsetPlacement N q hq y.2.1.2 B) := by
  rw [arbitraryN_product_eq_actualPairPlacementSum]
  let F := fun z : ActualPairPlacement N p q =>
    (arbitraryNSectorSubsetPlacement N p hp z.1 A).comp
      (arbitraryNSectorSubsetPlacement N q hq z.2 B)
  have hprod :
      (∑ S : PlacementSubset p (N - p),
        ∑ T : PlacementSubset q (N - q),
          (arbitraryNSectorSubsetPlacement N p hp S A).comp
            (arbitraryNSectorSubsetPlacement N q hq T B)) =
        ∑ z : ActualPairPlacement N p q, F z := by
    simpa [F, ActualPairPlacement] using
      (Fintype.sum_prod_type' (fun S T =>
        (arbitraryNSectorSubsetPlacement N p hp S A).comp
          (arbitraryNSectorSubsetPlacement N q hq T B))).symm
  rw [hprod, actualPairOperatorSum_eq_unionFibers]

/-- The exact source normalization after choosing a union subset and averaging
over its actual local overlap configurations. The final factor is precisely
the reciprocal of the two source placement counts. -/
theorem overlapFiber_pairNormalization
    {N p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (hr : unionSize p q s ≤ N) :
    overlapCoefficient N p q s *
        (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℝ)⁻¹ *
        (Nat.choose N (unionSize p q s) : ℝ)⁻¹ =
      ((Nat.choose N p : ℝ) * (Nat.choose N q : ℝ))⁻¹ := by
  have hlocal := overlapCoefficient_mul_localAverageFactor hsp hsq hr
  have hchoose : (Nat.choose N (unionSize p q s) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hr
  have hden :
      (Nat.choose N p : ℝ) * (Nat.choose N q : ℝ) ≠ 0 := by
    apply mul_ne_zero
    · have hp : p ≤ N := by dsimp [unionSize] at hr; omega
      exact_mod_cast Nat.choose_ne_zero hp
    · have hq : q ≤ N := by dsimp [unionSize] at hr; omega
      exact_mod_cast Nat.choose_ne_zero hq
  calc
    _ = (overlapCoefficient N p q s *
          (Fintype.card (OverlapConfiguration p q s hsp hsq) : ℝ)⁻¹) *
          (Nat.choose N (unionSize p q s) : ℝ)⁻¹ := by ring
    _ = ((Nat.choose N (unionSize p q s) : ℝ) /
          ((Nat.choose N p : ℝ) * (Nat.choose N q : ℝ))) *
          (Nat.choose N (unionSize p q s) : ℝ)⁻¹ := by rw [hlocal]
    _ = _ := by
      field_simp [hchoose, hden]

/-- The frozen averaged overlap kernel, expanded as the genuine finite
average of the compressed ordered placement products on the union slots. -/
theorem averagedOverlapKernel_eq_concreteLocalPairAverage
    {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    averagedOverlapKernel hsp hsq A B =
      ((Fintype.card (OverlapConfiguration p q s hsp hsq) : ℂ)⁻¹) •
        ∑ C : OverlapConfiguration p q s hsp hsq,
          (symProjToSector (unionSize p q s)).comp
            (((subsetPlacement C.left A).comp (rightPlacement C B)).comp
              (SymSector ℂ H (unionSize p q s)).subtypeL) := by
  rw [averagedOverlapKernel_eq_average]
  rfl

#print axioms QuantumNLS.PlacementUnionReindex.pairPlacementKey
#print axioms QuantumNLS.PlacementUnionReindex.pairPlacementBase_unionSize_le_N
#print axioms QuantumNLS.PlacementUnionReindex.pairPlacementUnionEquiv
#print axioms QuantumNLS.PlacementUnionReindex.sum_pairPlacement_eq_sum_unionFibers
#print axioms QuantumNLS.PlacementUnionReindex.actualPairOperatorSum_eq_unionFibers
#print axioms QuantumNLS.PlacementUnionReindex.genericU_product_eq_unionFiberSum
#print axioms QuantumNLS.PlacementUnionReindex.overlapFiber_pairNormalization
#print axioms QuantumNLS.PlacementUnionReindex.averagedOverlapKernel_eq_concreteLocalPairAverage

end QuantumNLS.PlacementUnionReindex


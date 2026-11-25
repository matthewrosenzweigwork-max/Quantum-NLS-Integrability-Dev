/-
QuantumNLS.PlacementOverlap — concrete overlap configurations and fibers.

This continuation starts from the frozen actual placement construction in
PlacementFusion.  The finite counting below concerns actual subsets of tensor
slots; it does not postulate a fusion identity.
-/
import QuantumNLS.PlacementFusion

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion

noncomputable section

namespace QuantumNLS.PlacementOverlap

/-- The q-subsets whose actual intersection with a fixed set P has size s. -/
def overlapFiber {N : ℕ} (P : Finset (Fin N)) (q s : ℕ) : Finset (Finset (Fin N)) :=
  ((Finset.univ : Finset (Fin N)).powersetCard q).filter
    (fun Q => (P ∩ Q).card = s)

/-- Choose the s points of P and the remaining q-s points outside P. -/
def overlapDecompositions {N : ℕ} (P : Finset (Fin N)) (q s : ℕ) :
    Finset (Finset (Fin N) × Finset (Fin N)) :=
  P.powersetCard s ×ˢ ((Finset.univ \ P).powersetCard (q - s))

private theorem inter_join_eq_left {N : ℕ} {P S T : Finset (Fin N)}
    (hS : S ⊆ P) (hT : T ⊆ Finset.univ \ P) :
    (S ∪ T) ∩ P = S := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hST, hxP⟩
    rcases hST with hxS | hxT
    · exact hxS
    · exact False.elim ((Finset.mem_sdiff.mp (hT hxT)).2 hxP)
  · intro hxS
    exact ⟨Or.inl hxS, hS hxS⟩

private theorem sdiff_join_eq_right {N : ℕ} {P S T : Finset (Fin N)}
    (hS : S ⊆ P) (hT : T ⊆ Finset.univ \ P) :
    (S ∪ T) \ P = T := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hxS | hxT, hxP⟩
    · exact False.elim (hxP (hS hxS))
    · exact hxT
  · intro hxT
    exact ⟨Or.inr hxT, (Finset.mem_sdiff.mp (hT hxT)).2⟩

private theorem card_join_eq {N : ℕ} {P S T : Finset (Fin N)}
    (hS : S ⊆ P) (hT : T ⊆ Finset.univ \ P)
    (hScard : S.card = s) (hTcard : T.card = q - s) (hsq : s ≤ q) :
    (S ∪ T).card = q := by
  have hdisj : Disjoint S T := Finset.disjoint_left.mpr fun x hxS hxT =>
    (Finset.mem_sdiff.mp (hT hxT)).2 (hS hxS)
  rw [Finset.card_union_of_disjoint hdisj, hScard, hTcard]
  omega

/-- Every member of the fixed-P overlap fiber is uniquely the union of its
actual intersection with P and its actual difference from P. -/
theorem overlapFiber_eq_decomposition_image {N q s : ℕ}
    (P : Finset (Fin N)) (hsq : s ≤ q) :
    overlapFiber P q s =
      (overlapDecompositions P q s).image (fun st => st.1 ∪ st.2) := by
  classical
  ext Q
  constructor
  · intro hQ
    rcases Finset.mem_filter.mp hQ with ⟨hQsub, hinter⟩
    have hQcard : Q.card = q := (Finset.mem_powersetCard.mp hQsub).2
    let S := P ∩ Q
    let T := Q \ P
    have hScard : S.card = s := by simpa [S] using hinter
    have hTcard : T.card = q - s := by
      have hcard := Finset.card_inter_add_card_sdiff Q P
      have hcomm : (Q ∩ P).card = s := by simpa [Finset.inter_comm] using hinter
      rw [hcomm, hQcard] at hcard
      dsimp [T]
      omega
    have hSsub : S ⊆ P := Finset.inter_subset_left
    have hTsub : T ⊆ Finset.univ \ P := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
    have hjoin : S ∪ T = Q := by
      ext x
      by_cases hxP : x ∈ P <;> simp [S, T, hxP]
    apply Finset.mem_image.mpr
    refine ⟨(S, T), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hSsub, hScard⟩,
         Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩⟩
    · simpa using hjoin
  · intro hQ
    rcases Finset.mem_image.mp hQ with ⟨⟨S, T⟩, hST, rfl⟩
    rcases Finset.mem_product.mp hST with ⟨hS, hT⟩
    rcases Finset.mem_powersetCard.mp hS with ⟨hSsub, hScard⟩
    rcases Finset.mem_powersetCard.mp hT with ⟨hTsub, hTcard⟩
    have hQcard : (S ∪ T).card = q := card_join_eq hSsub hTsub hScard hTcard hsq
    have hQsub : S ∪ T ⊆ Finset.univ := Finset.subset_univ _
    have hinter' : (P ∩ (S ∪ T)).card = s := by
      have h := inter_join_eq_left hSsub hTsub
      have h' : P ∩ (S ∪ T) = S := by simpa [Finset.inter_comm] using h
      rw [h', hScard]
    rw [overlapFiber, Finset.mem_filter]
    exact ⟨Finset.mem_powersetCard.mpr ⟨hQsub, hQcard⟩,
      hinter'⟩

private theorem union_injOn_decompositions {N : ℕ} {P : Finset (Fin N)}
    {q s : ℕ} :
    Set.InjOn (fun st : Finset (Fin N) × Finset (Fin N) => st.1 ∪ st.2)
      (overlapDecompositions P q s) := by
  intro a ha b hb hab
  have ha' := Finset.mem_product.mp ha
  have hb' := Finset.mem_product.mp hb
  have haS := (Finset.mem_powersetCard.mp ha'.1).1
  have haT := (Finset.mem_powersetCard.mp ha'.2).1
  have hbS := (Finset.mem_powersetCard.mp hb'.1).1
  have hbT := (Finset.mem_powersetCard.mp hb'.2).1
  have hleft : a.1 = b.1 := by
    have h := congrArg (fun X : Finset (Fin N) => X ∩ P) hab
    simpa [inter_join_eq_left haS haT, inter_join_eq_left hbS hbT] using h
  have hright : a.2 = b.2 := by
    have h := congrArg (fun X : Finset (Fin N) => X \ P) hab
    simpa [sdiff_join_eq_right haS haT, sdiff_join_eq_right hbS hbT] using h
  exact Prod.ext hleft hright

/-- The fixed-p overlap fiber has exactly the source numerator many members.
The proof counts actual q-subsets by the disjoint decomposition `Q=(Q∩P)∪(Q\P)`.
-/
theorem card_overlapFiber {N p q s : ℕ} (P : Finset (Fin N))
    (hP : P.card = p) (hsq : s ≤ q) :
    (overlapFiber P q s).card = Nat.choose p s * Nat.choose (N - p) (q - s) := by
  classical
  rw [overlapFiber_eq_decomposition_image P hsq]
  rw [Finset.card_image_of_injOn (union_injOn_decompositions (P := P))]
  have hcomp : (Finset.univ \ P).card = N - p := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ P)]
    simp [Finset.card_univ, hP]
  simp [overlapDecompositions, Finset.card_product, Finset.card_powersetCard, hcomp, hP]

/-- A pair of actual subsets of a fixed N-slot tensor power with a specified
intersection size. -/
structure ActualOverlapConfiguration (N p q s : ℕ) where
  left : Finset (Fin N)
  right : Finset (Fin N)
  left_card : left.card = p
  right_card : right.card = q
  intersection_card : (left ∩ right).card = s

/-- The union size is forced by the actual intersection size. -/
theorem ActualOverlapConfiguration.union_card {N p q s : ℕ}
    (C : ActualOverlapConfiguration N p q s) : (C.left ∪ C.right).card = p + q - s := by
  have h := Finset.card_inter_add_card_union C.left C.right
  rw [C.left_card, C.right_card, C.intersection_card] at h
  omega

/-- Relabel every tensor slot by one permutation. -/
def relabelConfiguration {N p q s : ℕ} (σ : Equiv.Perm (Fin N))
    (C : ActualOverlapConfiguration N p q s) : ActualOverlapConfiguration N p q s where
  left := C.left.map σ.toEmbedding
  right := C.right.map σ.toEmbedding
  left_card := by simpa using C.left_card
  right_card := by simpa using C.right_card
  intersection_card := by
    rw [← Finset.map_inter, Finset.card_map]
    exact C.intersection_card

/-- Slot relabeling preserves the actual union cardinality as well. -/
theorem relabelConfiguration_union_card {N p q s : ℕ}
    (σ : Equiv.Perm (Fin N)) (C : ActualOverlapConfiguration N p q s) :
    ((relabelConfiguration σ C).left ∪ (relabelConfiguration σ C).right).card =
      p + q - s :=
  (relabelConfiguration σ C).union_card

/-- For feasible parameters, an actual overlap configuration exists in the
literal N-slot set. Its right set is selected from the counted fixed-left
overlap fiber. -/
theorem exists_actualOverlapConfiguration {N p q s : ℕ}
    (hp : p ≤ N) (hsP : s ≤ p) (hsq : s ≤ q) (hrest : q - s ≤ N - p) :
    ∃ C : ActualOverlapConfiguration N p q s,
      C.left = Finset.univ.map (Fin.castLEEmb hp) := by
  classical
  let P : Finset (Fin N) := Finset.univ.map (Fin.castLEEmb hp)
  have hP : P.card = p := by simp [P]
  have hpos : 0 < (overlapFiber P q s).card := by
    rw [card_overlapFiber P hP hsq]
    exact Nat.mul_pos (Nat.choose_pos hsP) (Nat.choose_pos hrest)
  obtain ⟨Q, hQ⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_filter.mp hQ with ⟨hQsub, hinter⟩
  refine ⟨⟨P, Q, hP, (Finset.mem_powersetCard.mp hQsub).2, hinter⟩, ?_⟩
  rfl

/-- The source overlap coefficient is the fraction of q-subsets in the
fixed-p overlap fiber. Its binomial numerator is derived from the count of
actual placements. -/
theorem overlapCoefficient_eq_fiberProbability {N p q s : ℕ}
    (P : Finset (Fin N)) (hP : P.card = p) (hsq : s ≤ q) :
    overlapCoefficient N p q s =
      ((overlapFiber P q s).card : ℝ) / (Nat.choose N q : ℝ) := by
  simp [overlapCoefficient, hsq, card_overlapFiber P hP hsq]

/-- The actual overlap fibers partition the q-subsets, so their source
probabilities retain the exact binomial normalization. -/
theorem sum_overlapFiberProbability_eq_one {N p q : ℕ}
    (P : Finset (Fin N)) (hP : P.card = p) (hp : p ≤ N) (hq : q ≤ N) :
    (∑ s ∈ Finset.range (q + 1),
      ((overlapFiber P q s).card : ℝ) / (Nat.choose N q : ℝ)) = 1 := by
  calc
    _ = ∑ s ∈ Finset.range (q + 1), overlapCoefficient N p q s := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsq : s ≤ q := by
        have hlt := Finset.mem_range.mp hs
        omega
      exact (overlapCoefficient_eq_fiberProbability P hP hsq).symm
    _ = 1 := sum_overlapCoefficient_eq_one hp hq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A single actual subset placement, compressed to the symmetric sector at
the union tensor size. -/
def actualSectorSubsetPlacement {p q : ℕ}
    (S : PlacementSubset p q) (A : BoundedSymmetricKernel H p) :
    SymSector ℂ H (p + q) →L[ℂ] SymSector ℂ H (p + q) :=
  (symProjToSector (p + q)).comp
    ((subsetPlacement S A).comp (SymSector ℂ H (p + q)).subtypeL)

/-- The source-normalized average of the actual compressed subset placements. -/
def actualSectorSubsetAverage {p q : ℕ}
    (A : BoundedSymmetricKernel H p) :
    SymSector ℂ H (p + q) →L[ℂ] SymSector ℂ H (p + q) :=
  ((Nat.choose (p + q) p : ℂ)⁻¹) •
    ∑ S : PlacementSubset p q, actualSectorSubsetPlacement S A

/-- Averaging the individually compressed actual placements is exactly the
literal DEF-041 subset average restricted to the symmetric sector. -/
theorem actualSectorSubsetAverage_eq_subsetPlacementAverage {p q : ℕ}
    (A : BoundedSymmetricKernel H p) :
    actualSectorSubsetAverage A =
      ((subsetPlacementAverage (q := q) A).comp
        (SymSector ℂ H (p + q)).subtypeL).codRestrict (SymSector ℂ H (p + q))
          (subsetPlacementAverage_apply_mem A) := by
  ext x
  have hmem := subsetPlacementAverage_apply_mem (q := q) A x
  dsimp [actualSectorSubsetAverage, actualSectorSubsetPlacement]
  simp only [smul_apply, sum_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]
  calc
    _ = (symProjToSector (p + q)
          (((Nat.choose (p + q) p : ℂ)⁻¹) •
            ∑ S : PlacementSubset p q, subsetPlacement S A x.1)).1 := by
          simp only [map_smul, map_sum]
    _ = (symProjToSector (p + q)
          (subsetPlacementAverage (q := q) A x.1)).1 := by
          simp only [subsetPlacementAverage, smul_apply, sum_apply]
    _ = subsetPlacementAverage (q := q) A x.1 := by
          change symProj ℂ H (p + q) _ = _
          change groupAverage (permRep ℂ H (p + q)) _ = _
          exact groupAverage_apply_of_mem (permRep ℂ H (p + q)) hmem

omit [CompleteSpace H] in
/-- Casting a finite sum of operators between equal symmetric-sector indices
commutes with scalar multiplication and summation. -/
private theorem castSymSectorOperator_smul_sum {m n : ℕ} (h : m = n)
    {ι : Type*} [Fintype ι] (c : ℂ)
    (F : ι → SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    castSymSectorOperator h (c • ∑ i, F i) =
      c • ∑ i, castSymSectorOperator h (F i) := by
  cases h
  rfl

/-- One actual p-placement on the N-particle symmetric sector, with only its
canonical particle-count reindexing applied. -/
def arbitraryNSectorSubsetPlacement (N p : ℕ) (hp : p ≤ N)
    (S : PlacementSubset p (N - p)) (A : BoundedSymmetricKernel H p) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  castSymSectorOperator (Nat.add_sub_of_le hp)
    (actualSectorSubsetPlacement S A)

/-- The source-normalized finite average of the actual p-subset placements
on the literal N-particle sector. -/
def arbitraryNSectorSubsetAverage (N p : ℕ) (hp : p ≤ N)
    (A : BoundedSymmetricKernel H p) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  ((Nat.choose N p : ℂ)⁻¹) •
    ∑ S : PlacementSubset p (N - p), arbitraryNSectorSubsetPlacement N p hp S A

/-- The literal source operator is the source-normalized average of its
concrete compressed subset placements. -/
theorem genericU_N_r_eq_arbitraryNSectorSubsetAverage
    (N p : ℕ) (hp : p ≤ N) (A : BoundedSymmetricKernel H p) :
    genericU_N_r N p hp A = arbitraryNSectorSubsetAverage N p hp A := by
  rw [genericU_N_r_eq_subsetPlacementAverage]
  unfold genericSubsetPlacementAverage arbitraryNSectorSubsetAverage
  have hsector := actualSectorSubsetAverage_eq_subsetPlacementAverage
    (q := N - p) A
  have hcast := castSymSectorOperator_smul_sum
    (H := H) (Nat.add_sub_of_le hp) (Nat.choose N p : ℂ)⁻¹
      (fun S : PlacementSubset p (N - p) => actualSectorSubsetPlacement S A)
  rw [← hsector]
  unfold actualSectorSubsetAverage
  have hchoose : Nat.choose (p + (N - p)) p = Nat.choose N p :=
    congrArg (fun n => Nat.choose n p) (Nat.add_sub_of_le hp)
  rw [hchoose]
  simp only [arbitraryNSectorSubsetPlacement]
  exact hcast

/-- Bilinearity expands the product of two finite operator averages as the
actual pair-placement sum. -/
theorem smul_sum_comp_smul_sum {X ι κ : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι] [Fintype κ]
    (c d : ℂ) (F : ι → X →L[ℂ] X) (G : κ → X →L[ℂ] X) :
    ((c • ∑ i, F i).comp (d • ∑ j, G j)) =
      (c * d) • ∑ i, ∑ j, (F i).comp (G j) := by
  ext x
  simp [ContinuousLinearMap.comp_apply, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [mul_comm, smul_smul]

/-- Arbitrary-N product expansion into the actual independently chosen
p- and q-subset placement products. The two reciprocal binomial factors are
the source normalization; no universal fusion kernel is assumed here. -/
theorem arbitraryN_product_eq_actualPairPlacementSum
    (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) :
    (genericU_N_r N p hp A).comp (genericU_N_r N q hq B) =
      (((Nat.choose N p : ℂ)⁻¹) * ((Nat.choose N q : ℂ)⁻¹)) •
        ∑ S : PlacementSubset p (N - p),
          ∑ T : PlacementSubset q (N - q),
            (arbitraryNSectorSubsetPlacement N p hp S A).comp
              (arbitraryNSectorSubsetPlacement N q hq T B) := by
  rw [genericU_N_r_eq_arbitraryNSectorSubsetAverage,
    genericU_N_r_eq_arbitraryNSectorSubsetAverage]
  exact smul_sum_comp_smul_sum
    ((Nat.choose N p : ℂ)⁻¹) ((Nat.choose N q : ℂ)⁻¹)
    (fun S : PlacementSubset p (N - p) => arbitraryNSectorSubsetPlacement N p hp S A)
    (fun T : PlacementSubset q (N - q) => arbitraryNSectorSubsetPlacement N q hq T B)

end QuantumNLS.PlacementOverlap

#print axioms QuantumNLS.PlacementOverlap.overlapFiber_eq_decomposition_image
#print axioms QuantumNLS.PlacementOverlap.card_overlapFiber
#print axioms QuantumNLS.PlacementOverlap.ActualOverlapConfiguration.union_card
#print axioms QuantumNLS.PlacementOverlap.relabelConfiguration
#print axioms QuantumNLS.PlacementOverlap.relabelConfiguration_union_card
#print axioms QuantumNLS.PlacementOverlap.exists_actualOverlapConfiguration
#print axioms QuantumNLS.PlacementOverlap.overlapCoefficient_eq_fiberProbability
#print axioms QuantumNLS.PlacementOverlap.sum_overlapFiberProbability_eq_one
#print axioms QuantumNLS.PlacementOverlap.actualSectorSubsetAverage_eq_subsetPlacementAverage
#print axioms QuantumNLS.PlacementOverlap.genericU_N_r_eq_arbitraryNSectorSubsetAverage
#print axioms QuantumNLS.PlacementOverlap.arbitraryN_product_eq_actualPairPlacementSum

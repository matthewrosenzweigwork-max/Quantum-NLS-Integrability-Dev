import QuantumNLS.BetheSourceCrossing
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.Fin

/-! Finite chamber charts and permutation multiplicities. These are index
identities. Identifying the multivariable physical integral's boundary terms
with this index system is a separate, still open, analytic obligation. -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheFaceEnumeration
open TensorPlacements

theorem complement_card {m q : ℕ} (S : PlacementSubset m q) :
    S.1ᶜ.card = q := by
  rw [Finset.card_compl, Fintype.card_fin, S.2]
  omega

/-- Put the selected and spectator lists in their increasing chamber ranks.
Unlike an arbitrary placement representative, both blocks preserve order. -/
def mergePermutation {m q : ℕ} (S : PlacementSubset m q) :
    Equiv.Perm (Fin (m+q)) := by
  classical
  let f : Fin (m+q) → Fin (m+q) := Fin.addCases
    (S.1.orderEmbOfFin S.2) (S.1ᶜ.orderEmbOfFin (complement_card S))
  have hinj : Function.Injective f := by
    intro i j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
      refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;> intro h
    · have he : S.1.orderEmbOfFin S.2 a = S.1.orderEmbOfFin S.2 b := by simpa [f] using h
      exact congrArg (Fin.castAdd q) ((S.1.orderEmbOfFin S.2).injective he)
    · have ha := S.1.orderEmbOfFin_mem S.2 a
      have hb := S.1ᶜ.orderEmbOfFin_mem (complement_card S) b
      have he : S.1.orderEmbOfFin S.2 a = S.1ᶜ.orderEmbOfFin (complement_card S) b := by simpa [f] using h
      exact False.elim ((Finset.mem_compl.mp hb) (he ▸ ha))
    · have ha := S.1ᶜ.orderEmbOfFin_mem (complement_card S) a
      have hb := S.1.orderEmbOfFin_mem S.2 b
      have he : S.1ᶜ.orderEmbOfFin (complement_card S) a = S.1.orderEmbOfFin S.2 b := by simpa [f] using h
      exact False.elim ((Finset.mem_compl.mp ha) (he.symm ▸ hb))
    · have he : S.1ᶜ.orderEmbOfFin (complement_card S) a = S.1ᶜ.orderEmbOfFin (complement_card S) b := by simpa [f] using h
      exact congrArg (Fin.natAdd m) ((S.1ᶜ.orderEmbOfFin (complement_card S)).injective he)
  exact Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)

theorem mergePermutation_selected {m q : ℕ} (S : PlacementSubset m q) (i : Fin m) :
    mergePermutation S (Fin.castAdd q i) = S.1.orderEmbOfFin S.2 i := by
  simp [mergePermutation]

theorem mergePermutation_spectator {m q : ℕ} (S : PlacementSubset m q) (i : Fin q) :
    mergePermutation S (Fin.natAdd m i) = S.1ᶜ.orderEmbOfFin (complement_card S) i := by
  simp [mergePermutation]

theorem mergePermutation_image {m q : ℕ} (S : PlacementSubset m q) :
    placementSubsetOfPerm (mergePermutation S) = S := by
  classical
  apply Subtype.ext
  ext x
  simp only [placementSubsetOfPerm, Finset.mem_map, mem_firstPositions]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    change mergePermutation S (Fin.castAdd q i) ∈ S.1
    rw [mergePermutation_selected]
    exact S.1.orderEmbOfFin_mem S.2 i
  · intro hx
    obtain ⟨i, hi⟩ := (S.1.orderIsoOfFin S.2).surjective ⟨x,hx⟩
    refine ⟨Fin.castAdd q i, ⟨i,rfl⟩, ?_⟩
    change mergePermutation S (Fin.castAdd q i) = x
    rw [mergePermutation_selected]
    exact congrArg Subtype.val hi

/-- Every chamber shuffle has exactly one order-preserving representative. -/
theorem mergePermutation_unique {m q : ℕ} (S : PlacementSubset m q)
    (σ : Equiv.Perm (Fin (m+q))) (hS : placementSubsetOfPerm σ = S)
    (hm : StrictMono (fun i : Fin m => σ (Fin.castAdd q i)))
    (hq : StrictMono (fun i : Fin q => σ (Fin.natAdd m i))) :
    σ = mergePermutation S := by
  classical
  have hmem (i : Fin m) : σ (Fin.castAdd q i) ∈ S.1 := by
    rw [← hS]
    exact Finset.mem_map.mpr ⟨_, (mem_firstPositions _).mpr ⟨i,rfl⟩, rfl⟩
  have hnmem (i : Fin q) : σ (Fin.natAdd m i) ∈ S.1ᶜ := by
    rw [Finset.mem_compl, ← hS]
    rintro h
    obtain ⟨j,hj,he⟩ := Finset.mem_map.mp h
    obtain ⟨k,rfl⟩ := (mem_firstPositions j).mp hj
    have hval := congrArg Fin.val (σ.injective he)
    simp at hval
    omega
  have hm' := Finset.orderEmbOfFin_unique S.2 hmem hm
  have hq' := Finset.orderEmbOfFin_unique (complement_card S) hnmem hq
  apply Equiv.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [mergePermutation_selected]
    exact congrFun hm' j
  · rw [mergePermutation_spectator]
    exact congrFun hq' j

/-- Literal full-permutation regrouping for any subset-indexed quantity.
The value may include a face label or an evaluated face integral. -/
theorem sum_permutations_by_subset {m q : ℕ} (F : PlacementSubset m q → ℂ) :
    (∑ σ : Equiv.Perm (Fin (m+q)), F (placementSubsetOfPerm σ)) =
      ((m.factorial*q.factorial : ℕ) : ℂ) * ∑ S, F S := by
  classical
  rw [← Fintype.sum_fiberwise (placementSubsetOfPerm (p := m) (q := q))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  have he (σ : PlacementFiber S) : F (placementSubsetOfPerm σ.1) = F S := by rw [σ.2]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_placementFiber]

/-- The original physical coefficient, after the full permutation grouping.
The remaining m! belongs to the selected block, before its P_m average. -/
theorem physical_subset_coefficient (m q : ℕ) (c : ℝ) :
    (((c^m * (m+q).descFactorial m : ℝ) : ℂ) * ((m+q).factorial : ℂ)⁻¹) *
      ((m.factorial*q.factorial : ℕ) : ℂ) = (c : ℂ)^m * (m.factorial : ℂ) := by
  rw [BetheHigherPlacement.coefficient_normalization]
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  push_cast
  field_simp

/-- A nonempty chamber has N adjacent faces and exactly two outer faces. -/
abbrev ChamberFace (N : ℕ) := Fin N ⊕ Bool

def faceEquation {N : ℕ} (L : ℝ) (x : Fin (N+1) → ℝ) : ChamberFace N → Prop
  | Sum.inl j => x j.castSucc = x j.succ
  | Sum.inr false => x 0 = L
  | Sum.inr true => x (Fin.last N) = 0

theorem card_chamberFace (N : ℕ) : Fintype.card (ChamberFace N) = N+2 := by
  simp [ChamberFace]

/-- Exhaustion includes collisions at corners; several face equations may
hold simultaneously. This does not count a corner as an additional face. -/
theorem chamber_interior_or_face {N : ℕ} (L : ℝ) (x : Fin (N+1) → ℝ)
    (hx : Antitone x) (hb : ∀ i, x i ∈ Set.Icc 0 L) :
    (StrictAnti x ∧ ∀ i, x i ∈ Set.Ioo 0 L) ∨ ∃ f, faceEquation L x f := by
  classical
  by_cases h : ∃ f, faceEquation L x f
  · exact Or.inr h
  · left
    have hn (f : ChamberFace N) : ¬ faceEquation L x f := fun hf => h ⟨f,hf⟩
    constructor
    · apply Fin.strictAnti_iff_succ_lt.mpr
      intro j
      exact lt_of_le_of_ne (hx j.castSucc_le_succ) (Ne.symm (hn (Sum.inl j)))
    · intro i
      have hzero : 0 < x (Fin.last N) := lt_of_le_of_ne (hb _).1 (Ne.symm (hn (Sum.inr true)))
      have hL : x 0 < L := lt_of_le_of_ne (hb _).2 (hn (Sum.inr false))
      exact ⟨hzero.trans_le (hx (Fin.le_last i)), (hx (Fin.zero_le i)).trans_lt hL⟩

/-- Face labels do not alter the permutation-fiber multiplicity. This holds
at every degree including the empty and full selected blocks. -/
theorem sum_permutation_faces {m q N : ℕ}
    (F : PlacementSubset m q → ChamberFace N → ℂ) :
    (∑ σ : Equiv.Perm (Fin (m+q)), ∑ f, F (placementSubsetOfPerm σ) f) =
      ((m.factorial*q.factorial : ℕ) : ℂ) * ∑ S, ∑ f, F S f :=
  sum_permutations_by_subset (fun S => ∑ f, F S f)

/-- No omitted membership case at an internal face. The bits respectively
mean neither, right only, left only, and both coordinates are selected. -/
theorem internal_membership_cases {N : ℕ} (S : Finset (Fin (N+1))) (j : Fin N) :
    (j.castSucc ∉ S ∧ j.succ ∉ S) ∨
    (j.castSucc ∉ S ∧ j.succ ∈ S) ∨
    (j.castSucc ∈ S ∧ j.succ ∉ S) ∨
    (j.castSucc ∈ S ∧ j.succ ∈ S) := by
  classical
  by_cases ha : j.castSucc ∈ S <;> by_cases hb : j.succ ∈ S <;> simp [ha,hb]

/-- Each ordered spectator permutation is uniquely its distinguished label
and its residual permutation. This is an index count, not a geometric
identification of cross-degree boundary terms. -/
def spectatorDeletion (q : ℕ) :
    Equiv.Perm (Fin (q+1)) ≃ Fin (q+1) × Equiv.Perm (Fin q) :=
  Equiv.Perm.decomposeFin

theorem spectatorDeletion_label (q : ℕ) (ρ : Equiv.Perm (Fin (q+1))) :
    (spectatorDeletion q ρ).1 = ρ 0 := by
  obtain ⟨⟨j,τ⟩,rfl⟩ := (spectatorDeletion q).symm.surjective ρ
  simp [spectatorDeletion, Equiv.Perm.decomposeFin_symm_apply_zero]

theorem sum_spectator_deletion (q : ℕ)
    (F : Fin (q+1) → Equiv.Perm (Fin q) → ℂ) :
    (∑ ρ : Equiv.Perm (Fin (q+1)), F (spectatorDeletion q ρ).1 (spectatorDeletion q ρ).2) =
      ∑ j, ∑ τ, F j τ := by
  rw [(spectatorDeletion q).sum_comp (fun p => F p.1 p.2), Fintype.sum_prod_type]

theorem sum_spectator_labels (q : ℕ) (F : Fin (q+1) → ℂ) :
    (∑ ρ : Equiv.Perm (Fin (q+1)), F (ρ 0)) =
      (q.factorial : ℂ) * ∑ j, F j := by
  simp_rw [← spectatorDeletion_label]
  have he := sum_spectator_deletion q (fun j _ => F j)
  simpa [Fintype.card_perm, ← Finset.sum_mul, mul_comm] using he

/-- Full output permutations with a fixed selected subset and the selected
block in chamber order. Spectators are still fully labelled. -/
abbrev OrderedFiber {m q : ℕ} (S : PlacementSubset m q) :=
  {σ : PlacementFiber S // StrictMono (fun i : Fin m => σ.1.1 (Fin.castAdd q i))}

def orderedFiberEquiv {m q : ℕ} (S : PlacementSubset m q) :
    Equiv.Perm (Fin q) ≃ OrderedFiber S := by
  classical
  let f : Equiv.Perm (Fin q) → OrderedFiber S := fun ρ =>
    ⟨⟨mergePermutation S * blockPerm (1 : Equiv.Perm (Fin m)) ρ, by
      apply Subtype.ext
      change (firstPositions (p := m) (q := q)).map
        (mergePermutation S * blockPerm (1 : Equiv.Perm (Fin m)) ρ).toEmbedding = S.1
      rw [show (firstPositions (p := m) (q := q)).map
          (mergePermutation S * blockPerm (1 : Equiv.Perm (Fin m)) ρ).toEmbedding =
          ((firstPositions (p := m) (q := q)).map (blockPerm (1 : Equiv.Perm (Fin m)) ρ).toEmbedding).map
            (mergePermutation S).toEmbedding by rw [Finset.map_map]; rfl,
        firstPositions_map_blockPerm]
      exact congrArg Subtype.val (mergePermutation_image S)⟩, by
        change StrictMono (fun i => mergePermutation S (blockPerm (1 : Equiv.Perm (Fin m)) ρ (Fin.castAdd q i)))
        simpa only [blockPerm_castAdd, Equiv.Perm.one_apply,
          mergePermutation_selected] using (S.1.orderEmbOfFin S.2).strictMono⟩
  have hinj : Function.Injective f := by
    intro ρ τ h
    have he : mergePermutation S * blockPerm (1 : Equiv.Perm (Fin m)) ρ = mergePermutation S * blockPerm (1 : Equiv.Perm (Fin m)) τ :=
      congrArg (fun z => z.1.1) h
    have hb := mul_left_cancel he
    apply Equiv.ext
    intro i
    have hi := congrArg (fun σ : Equiv.Perm (Fin (m+q)) => σ (Fin.natAdd m i)) hb
    exact (Fin.natAddEmb m).injective (by simpa only [blockPerm_natAdd, Fin.natAddEmb_apply] using hi)
  have hsurj : Function.Surjective f := by
    intro σ
    have himage : (firstPositions (p := m) (q := q)).map (mergePermutation S).toEmbedding =
        (firstPositions (p := m) (q := q)).map σ.1.1.toEmbedding :=
      (congrArg Subtype.val (mergePermutation_image S)).trans
        (congrArg Subtype.val σ.1.2).symm
    obtain ⟨π,ρ,hσ⟩ := exists_rightBlock_of_same_firstImage (mergePermutation S) σ.1.1 himage
    have hmono : StrictMono (π : Fin m → Fin m) := by
      intro i j hij
      have he := σ.2 hij
      rw [hσ] at he
      change mergePermutation S (blockPerm π ρ (Fin.castAdd q i)) <
        mergePermutation S (blockPerm π ρ (Fin.castAdd q j)) at he
      simpa only [blockPerm_castAdd, mergePermutation_selected,
        OrderEmbedding.lt_iff_lt] using he
    have hπ : π = 1 := Equiv.ext (congrFun hmono.eq_id)
    refine ⟨ρ, Subtype.ext (Subtype.ext ?_)⟩
    exact (hσ.trans (by rw [hπ])).symm
  exact Equiv.ofBijective f ⟨hinj,hsurj⟩

theorem card_orderedFiber {m q : ℕ} (S : PlacementSubset m q) :
    Fintype.card (OrderedFiber S) = q.factorial := by
  rw [← Fintype.card_congr (orderedFiberEquiv S)]
  simp [Fintype.card_perm]

/-- Every individual labelled face has multiplicity q! once the acted-on
output block is sorted. No degree-dependent factor is suppressed. -/
theorem sum_orderedFiber_face {m q : ℕ} (S : PlacementSubset m q) (v : ℂ) :
    (∑ _σ : OrderedFiber S, v) = (q.factorial : ℂ) * v := by
  simp [card_orderedFiber]

/-- The original physical coefficient times the ordered fiber is exactly
c^m. This count adds no m! to the printed transfer definition. -/
theorem physical_orderedFiber_coefficient {m q : ℕ} (S : PlacementSubset m q) (c : ℝ) :
    (((c^m * (m+q).descFactorial m : ℝ) : ℂ) * ((m+q).factorial : ℂ)⁻¹) *
      (Fintype.card (OrderedFiber S) : ℂ) = (c : ℂ)^m := by
  rw [card_orderedFiber, BetheHigherPlacement.coefficient_normalization]
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  field_simp

def mergeChart {m q : ℕ} (S : PlacementSubset m q) (y : Fin m → ℝ) (s : Fin q → ℝ) :
    Fin (m+q) → ℝ := Fin.append y s ∘ (mergePermutation S).symm

/-- Away from coordinate diagonals, the ordered selected and spectator
lists occupy exactly one merged chamber chart. This is a geometric cover
and uniqueness statement, before measure restriction or boundary gluing. -/
theorem exists_unique_mergeChart {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) (hinj : Function.Injective (Fin.append y s)) :
    ∃! S : PlacementSubset m q, Antitone (mergeChart S y s) := by
  classical
  let x := Fin.append y s
  let τ := Tuple.sort (α := ℝᵒᵈ) x
  let σ := τ.symm
  have hsort : Antitone (x ∘ τ) := BetheExtension.decreasing_antitone x
  have hm : StrictMono (fun i : Fin m => σ (Fin.castAdd q i)) := by
    intro i j hij
    by_contra h
    have hv := hsort (le_of_not_gt h)
    simp only [Function.comp_apply, σ, Equiv.apply_symm_apply, x, Fin.append_left] at hv
    exact (not_le_of_gt (hy hij)) hv
  have hq : StrictMono (fun i : Fin q => σ (Fin.natAdd m i)) := by
    intro i j hij
    by_contra h
    have hv := hsort (le_of_not_gt h)
    simp only [Function.comp_apply, σ, Equiv.apply_symm_apply, x, Fin.append_right] at hv
    exact (not_le_of_gt (hs hij)) hv
  let S := placementSubsetOfPerm (p := m) (q := q) σ
  have he : σ = mergePermutation S := mergePermutation_unique S σ rfl hm hq
  have hS : Antitone (mergeChart S y s) := by
    unfold mergeChart
    rw [← he]
    exact hsort
  refine ⟨S,hS,?_⟩
  intro T hT
  have hv : Fin.append y s ∘ (mergePermutation T).symm =
      Fin.append y s ∘ (mergePermutation S).symm := Tuple.unique_antitone hT hS
  have heq : (mergePermutation T).symm = (mergePermutation S).symm := by
    apply Equiv.ext
    intro i
    exact hinj (congrFun hv i)
  have heq' : mergePermutation T = mergePermutation S := by
    simpa only [Equiv.symm_symm] using congrArg Equiv.symm heq
  exact (mergePermutation_image T).symm.trans
    ((congrArg (placementSubsetOfPerm (p := m) (q := q)) heq').trans (mergePermutation_image S))

end QuantumNLS.BetheFaceEnumeration

#print axioms QuantumNLS.BetheFaceEnumeration.complement_card
#print axioms QuantumNLS.BetheFaceEnumeration.mergePermutation
#print axioms QuantumNLS.BetheFaceEnumeration.mergePermutation_selected
#print axioms QuantumNLS.BetheFaceEnumeration.mergePermutation_spectator
#print axioms QuantumNLS.BetheFaceEnumeration.mergePermutation_image
#print axioms QuantumNLS.BetheFaceEnumeration.mergePermutation_unique
#print axioms QuantumNLS.BetheFaceEnumeration.sum_permutations_by_subset
#print axioms QuantumNLS.BetheFaceEnumeration.physical_subset_coefficient
#print axioms QuantumNLS.BetheFaceEnumeration.ChamberFace
#print axioms QuantumNLS.BetheFaceEnumeration.faceEquation
#print axioms QuantumNLS.BetheFaceEnumeration.card_chamberFace
#print axioms QuantumNLS.BetheFaceEnumeration.chamber_interior_or_face
#print axioms QuantumNLS.BetheFaceEnumeration.sum_permutation_faces
#print axioms QuantumNLS.BetheFaceEnumeration.internal_membership_cases
#print axioms QuantumNLS.BetheFaceEnumeration.spectatorDeletion
#print axioms QuantumNLS.BetheFaceEnumeration.spectatorDeletion_label
#print axioms QuantumNLS.BetheFaceEnumeration.sum_spectator_deletion
#print axioms QuantumNLS.BetheFaceEnumeration.sum_spectator_labels
#print axioms QuantumNLS.BetheFaceEnumeration.OrderedFiber
#print axioms QuantumNLS.BetheFaceEnumeration.orderedFiberEquiv
#print axioms QuantumNLS.BetheFaceEnumeration.card_orderedFiber
#print axioms QuantumNLS.BetheFaceEnumeration.sum_orderedFiber_face
#print axioms QuantumNLS.BetheFaceEnumeration.physical_orderedFiber_coefficient
#print axioms QuantumNLS.BetheFaceEnumeration.mergeChart
#print axioms QuantumNLS.BetheFaceEnumeration.exists_unique_mergeChart

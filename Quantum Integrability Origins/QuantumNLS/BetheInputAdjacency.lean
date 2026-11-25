import QuantumNLS.BetheNeighborPromotion

/-! Pointwise input ordering at an actual mixed collision. Physical labels
are retained throughout. Strictness is imposed only on the physical output,
as in BGE1; moving coordinates and all other corners may coincide. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheInputAdjacency
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion

/-- The actual input-chart permutation in physical output labels. -/
def inputOrdering {m q : ℕ} (S T : PlacementSubset m q) :
    Equiv.Perm (Fin (m+q)) := (mergePermutation S).symm.trans (mergePermutation T)

/-- This ordering sees precisely the literal BGE1 merged input tuple. -/
theorem physicalInput_inputOrdering {m q : ℕ} (S T : PlacementSubset m q)
    (x y : Fin (m+q) → ℝ) :
    physicalInput x y S.1 ∘ (inputOrdering S T).symm =
      mergeChart T (fun i => y (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) := by
  classical
  funext k
  obtain ⟨l, rfl⟩ := (mergePermutation T).surjective k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) l
  · change physicalInput x y S.1 ((mergePermutation S)
        ((mergePermutation T).symm ((mergePermutation T) (Fin.castAdd q i)))) =
        Fin.append (fun i => y (S.1.orderEmbOfFin S.2 i))
          (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) ((mergePermutation T).symm ((mergePermutation T) (Fin.castAdd q i)))
    rw [Equiv.symm_apply_apply]
    rw [mergePermutation_selected]
    simp only [Fin.append_left]
    simp [physicalInput, S.1.orderEmbOfFin_mem S.2 i]
  · change physicalInput x y S.1 ((mergePermutation S)
        ((mergePermutation T).symm ((mergePermutation T) (Fin.natAdd m j)))) =
        Fin.append (fun i => y (S.1.orderEmbOfFin S.2 i))
          (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) ((mergePermutation T).symm ((mergePermutation T) (Fin.natAdd m j)))
    rw [Equiv.symm_apply_apply]
    rw [mergePermutation_spectator]
    simp only [Fin.append_right]
    simp [physicalInput, Finset.mem_compl.mp
      (S.1ᶜ.orderEmbOfFin_mem (complement_card S) j)]

/-- Every actual moving/spectator collision in the rectangle determines
the branch-oriented physical gap. It need not be supplied as a hypothesis. -/
theorem collision_internalGap {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hd : physicalDomain L x A y b) (ha : a ∈ A) (ht : t ∉ A)
    (he : y a = x t) : internalGap A a t b := by
  have hat : a ≠ t := fun h => ht (h ▸ ha)
  refine ⟨ha, ht, ?_⟩
  cases b
  · simp only [Bool.false_eq_true, ite_false] at hd ⊢
    have hat' : a < t := by
      rcases lt_or_gt_of_ne hat with h | h
      · exact h
      · have hh := (hd a ha).2.1
        rw [he] at hh
        exact False.elim ((not_le_of_gt (hx h)) hh)
    refine ⟨hat', ?_⟩
    intro k hk hkt
    by_contra hka
    have hak : a < k := lt_of_not_ge hka
    have hh := (hd a ha).2.2 k hk hak
    rw [he] at hh
    exact (not_le_of_gt (hx hkt)) hh
  · simp only [ite_true] at hd ⊢
    have hta : t < a := by
      rcases lt_or_gt_of_ne hat with h | h
      · have hh := (hd a ha).1
        rw [he] at hh
        exact False.elim ((not_le_of_gt (hx h)) hh)
      · exact h
    refine ⟨hta, ?_⟩
    intro k hk htk
    by_contra hak
    have hka : k < a := lt_of_not_ge hak
    have hh := (hd a ha).2.2 k hk hka
    rw [he] at hh
    exact (not_le_of_gt (hx htk)) hh

/-- At a mixed collision, every other physical input differs from that
value. Other collisions elsewhere are unrestricted. -/
theorem collision_isolated {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hd : physicalDomain L x A y b) (ha : a ∈ A) (ht : t ∉ A)
    (he : y a = x t) :
    ∀ k, k ≠ a → k ≠ t → physicalInput x y A k ≠ x t := by
  classical
  have hg := collision_internalGap L x y hx A a t b hd ha ht he
  intro k hka hkt
  by_cases hk : k ∈ A
  · simp only [physicalInput, ite_eq_left hk]
    cases b
    · simp only [physicalDomain, internalGap, Bool.false_eq_true, ite_false] at hd hg
      rcases lt_or_gt_of_ne hka with hka | hak
      · have hh := (hd k hk).2.2 a ha hka
        exact ne_of_gt ((hx hg.2.2.1).trans_le hh)
      · have htk : t < k := by
          rcases lt_or_gt_of_ne hkt with hkt | htk
          · exact False.elim ((not_le_of_gt hak) (hg.2.2.2 k hk hkt))
          · exact htk
        exact ne_of_lt (((hd k hk).2.1).trans_lt (hx htk))
    · simp only [physicalDomain, internalGap, ite_true] at hd hg
      rcases lt_or_gt_of_ne hka with hka | hak
      · have hkt : k < t := by
          rcases lt_or_gt_of_ne hkt with hkt | htk
          · exact hkt
          · exact False.elim ((not_le_of_gt hka) (hg.2.2.2 k hk htk))
        exact ne_of_gt ((hx hkt).trans_le (hd k hk).1)
      · have hh := (hd k hk).2.2 a ha hak
        exact ne_of_lt (hh.trans_lt (hx hg.2.2.1))
  · simp only [physicalInput, ite_eq_right hk]
    exact fun h => hkt (hx.injective h)

/-- In an antitone permutation, an isolated double value occupies two
consecutive ranks. This counts labels, without choosing a tie convention. -/
theorem isolated_pair_adjacent {N : ℕ} (v : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (hs : Antitone (v ∘ π.symm))
    (a t : Fin N) (_hat : a ≠ t) (he : v a = v t)
    (hi : ∀ k, k ≠ a → k ≠ t → v k ≠ v t)
    (ho : π a < π t) : (π t).val = (π a).val+1 := by
  by_contra hn
  have hp : (π a).val < (π t).val := ho
  have hmid : (π a).val+1 < N := by have := (π t).isLt; omega
  let j : Fin N := ⟨(π a).val+1, hmid⟩
  have haj : π a < j := by change (π a).val < (π a).val+1; omega
  have hjt : j < π t := by change (π a).val+1 < (π t).val; omega
  have hja : π.symm j ≠ a := by
    intro h
    have hh := congrArg π h
    simp only [Equiv.apply_symm_apply] at hh
    exact (ne_of_gt haj) hh
  have hjt' : π.symm j ≠ t := by
    intro h
    have hh := congrArg π h
    simp only [Equiv.apply_symm_apply] at hh
    exact (ne_of_lt hjt) hh
  apply hi (π.symm j) hja hjt'
  apply le_antisymm
  · have hh := hs haj.le
    simpa [Function.comp_def, he] using hh
  · have hh := hs hjt.le
    simpa [Function.comp_def] using hh

/-- Adjacency is derived from actual rectangle support and sorted input,
including corners coincident away from the marked mixed collision. -/
theorem mixed_collision_adjacent {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hd : physicalDomain L x A y b) (ha : a ∈ A) (ht : t ∉ A)
    (he : y a = x t) (π : Equiv.Perm (Fin N))
    (hs : Antitone (physicalInput x y A ∘ π.symm)) :
    (π t).val = (π a).val+1 ∨ (π a).val = (π t).val+1 := by
  classical
  have hat : a ≠ t := fun h => ht (h ▸ ha)
  have hv : physicalInput x y A a = physicalInput x y A t := by
    simp [physicalInput, ha, ht, he]
  have hi : ∀ k, k ≠ a → k ≠ t →
      physicalInput x y A k ≠ physicalInput x y A t := by
    simpa [physicalInput, ht] using collision_isolated L x y hx A a t b hd ha ht he
  rcases lt_or_gt_of_ne (fun h => hat (π.injective h)) with ho | ho
  · exact Or.inl (isolated_pair_adjacent _ π hs a t hat hv hi ho)
  · right
    apply isolated_pair_adjacent _ π hs t a hat.symm hv.symm
    · intro k hkt hka h
      exact hi k hka hkt (h.trans hv)
    · exact ho

/-- Order within each of the two physical blocks. This permits ties in
their values but never changes their original labels. -/
def orderedBlocks {N : ℕ} (A : Finset (Fin N)) (π : Equiv.Perm (Fin N)) : Prop :=
  (∀ k ∈ A, ∀ l ∈ A, k < l → π k < π l) ∧
    (∀ k ∉ A, ∀ l ∉ A, k < l → π k < π l)

theorem inputOrdering_selected {m q : ℕ} (S T : PlacementSubset m q) (i : Fin m) :
    inputOrdering S T (S.1.orderEmbOfFin S.2 i) = T.1.orderEmbOfFin T.2 i := by
  rw [← mergePermutation_selected S i]
  simp only [inputOrdering, Equiv.trans_apply]
  rw [Equiv.symm_apply_apply, mergePermutation_selected]

theorem inputOrdering_spectator {m q : ℕ} (S T : PlacementSubset m q) (j : Fin q) :
    inputOrdering S T (S.1ᶜ.orderEmbOfFin (complement_card S) j) =
      T.1ᶜ.orderEmbOfFin (complement_card T) j := by
  rw [← mergePermutation_spectator S j]
  simp only [inputOrdering, Equiv.trans_apply]
  rw [Equiv.symm_apply_apply, mergePermutation_spectator]

theorem inputOrdering_orderedBlocks {m q : ℕ} (S T : PlacementSubset m q) :
    orderedBlocks S.1 (inputOrdering S T) := by
  have hex (k : Fin (m+q)) (hk : k ∈ S.1) :
      ∃ i : Fin m, S.1.orderEmbOfFin S.2 i = k := by
    exact ⟨(S.1.orderIsoOfFin S.2).symm ⟨k,hk⟩,
      congrArg Subtype.val ((S.1.orderIsoOfFin S.2).apply_symm_apply ⟨k,hk⟩)⟩
  have hec (k : Fin (m+q)) (hk : k ∉ S.1) :
      ∃ j : Fin q, S.1ᶜ.orderEmbOfFin (complement_card S) j = k := by
    exact ⟨(S.1ᶜ.orderIsoOfFin (complement_card S)).symm ⟨k,Finset.mem_compl.mpr hk⟩,
      congrArg Subtype.val ((S.1ᶜ.orderIsoOfFin (complement_card S)).apply_symm_apply
        ⟨k,Finset.mem_compl.mpr hk⟩)⟩
  constructor
  · intro k hk l hl hkl
    obtain ⟨i, rfl⟩ := hex k hk
    obtain ⟨j, rfl⟩ := hex l hl
    rw [inputOrdering_selected, inputOrdering_selected]
    exact (T.1.orderEmbOfFin T.2).strictMono
      ((S.1.orderEmbOfFin S.2).strictMono.lt_iff_lt.mp hkl)
  · intro k hk l hl hkl
    obtain ⟨i, rfl⟩ := hec k hk
    obtain ⟨j, rfl⟩ := hec l hl
    rw [inputOrdering_spectator, inputOrdering_spectator]
    exact (T.1ᶜ.orderEmbOfFin (complement_card T)).strictMono
      ((S.1ᶜ.orderEmbOfFin (complement_card S)).strictMono.lt_iff_lt.mp hkl)

/-- Physical block orderings are exactly the BGE1 input subsets, with
unique representatives. No extra permutation or stabilizer factor occurs. -/
def chartOrderingEquiv {m q : ℕ} (S : PlacementSubset m q) :
    PlacementSubset m q ≃ {π : Equiv.Perm (Fin (m+q)) // orderedBlocks S.1 π} := by
  classical
  apply Equiv.ofBijective (fun T => ⟨inputOrdering S T, inputOrdering_orderedBlocks S T⟩)
  constructor
  · intro T U h
    have he : inputOrdering S T = inputOrdering S U := congrArg Subtype.val h
    have hp : mergePermutation T = mergePermutation U := by
      apply Equiv.ext
      intro k
      have hh := congrArg (fun π : Equiv.Perm (Fin (m+q)) => π (mergePermutation S k)) he
      simpa only [inputOrdering, Equiv.trans_apply, Equiv.symm_apply_apply] using hh
    exact (mergePermutation_image T).symm.trans
      ((congrArg (placementSubsetOfPerm (p := m) (q := q)) hp).trans (mergePermutation_image U))
  · intro π
    let σ := (mergePermutation S).trans π.1
    let T := placementSubsetOfPerm (p := m) (q := q) σ
    have hm : StrictMono (fun i : Fin m => σ (Fin.castAdd q i)) := by
      intro i j hij
      change π.1 (mergePermutation S (Fin.castAdd q i)) <
        π.1 (mergePermutation S (Fin.castAdd q j))
      rw [mergePermutation_selected, mergePermutation_selected]
      exact π.2.1 _ (S.1.orderEmbOfFin_mem S.2 i) _ (S.1.orderEmbOfFin_mem S.2 j)
        ((S.1.orderEmbOfFin S.2).strictMono hij)
    have hq : StrictMono (fun i : Fin q => σ (Fin.natAdd m i)) := by
      intro i j hij
      change π.1 (mergePermutation S (Fin.natAdd m i)) <
        π.1 (mergePermutation S (Fin.natAdd m j))
      rw [mergePermutation_spectator, mergePermutation_spectator]
      exact π.2.2 _ (Finset.mem_compl.mp (S.1ᶜ.orderEmbOfFin_mem (complement_card S) i))
        _ (Finset.mem_compl.mp (S.1ᶜ.orderEmbOfFin_mem (complement_card S) j))
        ((S.1ᶜ.orderEmbOfFin (complement_card S)).strictMono hij)
    have hp := mergePermutation_unique T σ rfl hm hq
    refine ⟨T, Subtype.ext ?_⟩
    apply Equiv.ext
    intro k
    have hh := congrArg (fun e : Equiv.Perm (Fin (m+q)) => e ((mergePermutation S).symm k)) hp
    simpa only [σ, inputOrdering, Equiv.trans_apply, Equiv.apply_symm_apply] using hh.symm

/-- A strict inequality of literal input values fixes their rank order. -/
theorem sorted_rank_lt {N : ℕ} (v : Fin N → ℝ) (π : Equiv.Perm (Fin N))
    (hs : Antitone (v ∘ π.symm)) (k l : Fin N) (h : v l < v k) : π k < π l := by
  by_contra hn
  have hh := hs (le_of_not_gt hn)
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at hh
  exact (not_le_of_gt h) hh

/-- Demoting a selected label to its physical spectator preserves block
order whenever the literal input is sorted. Strict physical outputs ensure
the enlarged spectator block is ordered even at other moving collisions. -/
theorem orderedBlocks_demote {N : ℕ} (x y : Fin N → ℝ) (hx : StrictAnti x)
    (A : Finset (Fin N)) (t : Fin N) (_ht : t ∉ A) (π : Equiv.Perm (Fin N))
    (hs : Antitone (physicalInput x y A ∘ π.symm))
    (hp : orderedBlocks (insert t A) π) : orderedBlocks A π := by
  classical
  constructor
  · intro k hk l hl hkl
    exact hp.1 k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl) hkl
  · intro k hk l hl hkl
    exact sorted_rank_lt _ π hs k l (by simpa [physicalInput, hk, hl] using hx hkl)

/-- Promoting the marked label preserves the block order exactly in the
branch-oriented adjacent ordering. The proof uses the actual physical gap. -/
theorem orderedBlocks_promote {N : ℕ} (A : Finset (Fin N)) (a t : Fin N)
    (b : Bool) (hg : internalGap A a t b) (π : Equiv.Perm (Fin N))
    (hp : orderedBlocks A π)
    (hadj : if b then (π a).val = (π t).val+1 else (π t).val = (π a).val+1) :
    orderedBlocks (insert t A) π := by
  classical
  have hmono (k l : Fin N) (hk : k ∈ A) (hl : l ∈ A) (hkl : k ≤ l) :
      (π k).val ≤ (π l).val := by
    rcases lt_or_eq_of_le hkl with h | rfl
    · exact (hp.1 k hk l hl h).le
    · exact le_rfl
  have hne (k : Fin N) (hk : k ∈ A) : (π k).val ≠ (π t).val := by
    intro h
    exact hg.2.1 ((π.injective (Fin.ext h)) ▸ hk)
  constructor
  · intro k hk l hl hkl
    rcases Finset.mem_insert.mp hk with hkt | hk
    · subst k
      rcases Finset.mem_insert.mp hl with hlt | hl
      · subst l; exact False.elim (lt_irrefl _ hkl)
      · cases b
        · simp only [Bool.false_eq_true, ite_false] at hadj
          have hlt := hp.1 a hg.1 l hl (hg.2.2.1.trans hkl)
          have hn := hne l hl
          change (π a).val < (π l).val at hlt
          change (π t).val < (π l).val
          omega
        · simp only [ite_true] at hadj
          have hh := hmono a l hg.1 hl (hg.2.2.2 l hl hkl)
          change (π t).val < (π l).val
          omega
    · rcases Finset.mem_insert.mp hl with hlt | hl
      · subst l
        cases b
        · simp only [Bool.false_eq_true, ite_false] at hadj
          have hh := hmono k a hk hg.1 (hg.2.2.2 k hk hkl)
          change (π k).val < (π t).val
          omega
        · simp only [ite_true] at hadj
          have hlt := hp.1 k hk a hg.1 (hkl.trans hg.2.2.1)
          have hn := hne k hk
          change (π k).val < (π a).val at hlt
          change (π k).val < (π t).val
          omega
      · exact hp.1 k hk l hl hkl
  · intro k hk l hl hkl
    exact hp.2 k (fun h => hk (Finset.mem_insert_of_mem h))
      l (fun h => hl (Finset.mem_insert_of_mem h)) hkl

/-- The higher chart fixes the branch orientation of the derived adjacent
pair. No common-input adjacency or isolated-corner premise is assumed. -/
theorem promoted_chart_adjacent {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hd : physicalDomain L x A y b) (ha : a ∈ A) (ht : t ∉ A)
    (he : y a = x t) (π : Equiv.Perm (Fin N))
    (hs : Antitone (physicalInput x y A ∘ π.symm))
    (hp : orderedBlocks (insert t A) π) :
    if b then (π a).val = (π t).val+1 else (π t).val = (π a).val+1 := by
  have hg := collision_internalGap L x y hx A a t b hd ha ht he
  have hadj := mixed_collision_adjacent L x y hx A a t b hd ha ht he π hs
  have ha' : a ∈ insert t A := Finset.mem_insert_of_mem ha
  have ht' : t ∈ insert t A := Finset.mem_insert_self _ _
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    have hlt := hp.1 a ha' t ht' hg.2.2.1
    change (π a).val < (π t).val at hlt
    omega
  · simp only [ite_true]
    have hlt := hp.1 t ht' a ha' hg.2.2.1
    change (π t).val < (π a).val at hlt
    omega

/-- At the marked mixed collision, the same physical rank permutation
is a higher chart iff it is the branch-oriented member of the lower pair.
The underlying input tuple is exactly preserved by BNP1 promotion. -/
theorem incident_ordering_iff {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hd : physicalDomain L x A y b) (ha : a ∈ A) (ht : t ∉ A)
    (he : y a = x t) (π : Equiv.Perm (Fin N))
    (hs : Antitone (physicalInput x y A ∘ π.symm)) :
    orderedBlocks (insert t A) π ↔ orderedBlocks A π ∧
      (if b then π t < π a else π a < π t) := by
  constructor
  · intro hp
    refine ⟨orderedBlocks_demote x y hx A t ht π hs hp, ?_⟩
    have hadj := promoted_chart_adjacent L x y hx A a t b hd ha ht he π hs hp
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hadj ⊢ <;>
      change _ < _ <;> omega
  · rintro ⟨hp,ho⟩
    have hh := mixed_collision_adjacent L x y hx A a t b hd ha ht he π hs
    have hadj : if b then (π a).val = (π t).val+1 else (π t).val = (π a).val+1 := by
      cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at ho ⊢ <;>
        change _ < _ at ho <;> omega
    exact orderedBlocks_promote A a t b
      (collision_internalGap L x y hx A a t b hd ha ht he) π hp hadj

/-- Explicit identity inverse on the actual oriented incident input
orderings. Together with chartOrderingEquiv, these are genuine BGE1 chart
labels, rather than arbitrary sorting permutations or static counts.
This equivalence is at a fixed collision tuple; it does not yet identify
the clipped corner maps as functions of all endpoint labels. -/
def incidentOrderingEquiv {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hd : physicalDomain L x A y b) (ha : a ∈ A) (ht : t ∉ A)
    (he : y a = x t) :
    {π : Equiv.Perm (Fin N) //
      Antitone (physicalInput x y A ∘ π.symm) ∧ orderedBlocks A π ∧
        (if b then π t < π a else π a < π t)} ≃
    {π : Equiv.Perm (Fin N) //
      Antitone (physicalInput x (promoteTuple x y t) (insert t A) ∘ π.symm) ∧
        orderedBlocks (insert t A) π} := by
  rw [physicalInput_promote x y A t ht]
  exact Equiv.subtypeEquivRight (fun π => by
    constructor
    · rintro ⟨hs,hp⟩
      exact ⟨hs, (incident_ordering_iff L x y hx A a t b hd ha ht he π hs).mpr hp⟩
    · rintro ⟨hs,hp⟩
      exact ⟨hs, (incident_ordering_iff L x y hx A a t b hd ha ht he π hs).mp hp⟩)

/-- BNP1 local source balance with its common-input adjacency discharged
by the actual promoted chart geometry. All remaining signs, ranks, source
roots and coefficients are those of BNP1. -/
theorem source_promoted_face_balance_of_chart {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x y : Fin N → ℝ) (hx : StrictAnti x) (A : Finset (Fin N)) (a t : Fin N)
    (ha : a ∈ A) (ht : t ∉ A) (b : Bool) (hd : physicalDomain L x A y b)
    (he : y a = x t) (π : Equiv.Perm (Fin N))
    (hs : Antitone (physicalInput x y A ∘ π.symm))
    (hp : orderedBlocks (insert t A) π)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (ε : Fin N → Bool) (hea : ε a = b) (het : ε t = !b) :
    let r := BetheSmooth.sourceRoots L n c
    let w := physicalInput x y A ∘ π.symm
    let P := fun D => BetheInternalFaces.primitive c r w z (integratedRanks π D)
    let phase := Complex.exp (Complex.I*z*(physicalOffset L x y A b : ℂ))
    (c : ℂ)^A.card * phase * physicalOrientation (A.erase a) ε *
        (if b then P A - P (insert t (A.erase a))
          else P (insert t (A.erase a)) - P A) +
      (c : ℂ)^(A.card+1) * phase * physicalOrientation (insert t A) ε *
        P (insert t A) = 0 := by
  exact source_promoted_face_balance hL hc hn x y A a t ha ht he π b
    (promoted_chart_adjacent L x y hx A a t b hd ha ht he π hs hp) z hz ε hea het

/-- Promotion matches the literal sorted-chart domains pointwise on the
marked face. This includes empty residual sets and coincident corners. -/
theorem promoted_chart_domains_iff {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : Antitone x) (hb : ∀ k, x k ∈ Icc 0 L) (A : Finset (Fin N))
    (a t : Fin N) (b : Bool) (hg : internalGap A a t b) (he : y a = x t)
    (π : Equiv.Perm (Fin N)) :
    (physicalDomain L x (insert t A) (promoteTuple x y t) b ∧
      Antitone (physicalInput x (promoteTuple x y t) (insert t A) ∘ π.symm)) ↔
    (physicalDomain L x A y b ∧ Antitone (physicalInput x y A ∘ π.symm)) := by
  rw [physicalDomain_promote_iff L x y hx hb A a t b hg he,
    physicalInput_promote x y A t hg.2.1]

/-- Every actual generated corner belongs to its own closed physical cell,
including collapsed intervals. Empty boxes are excluded by the same guard
that BGE1 uses before generating any corner summands. -/
theorem generated_corner_mem_cell {m q : ℕ} (L : ℝ) (X : Fin m → ℝ)
    (s : Fin q → ℝ) (b : Bool) (T : PlacementSubset m q)
    (hX : X ∈ BetheWavefunctions.chamber m L) (hs : Antitone s)
    (hb : ∀ j, s j ∈ Icc 0 L)
    (hne : clipLower X s b T ≤ clipUpper L X s b T) (ε : Fin m → Bool) :
    cornerTuple (clipLower X s b T) (clipUpper L X s b T) ε ∈
      BetheChartFiberSteps.closedPhysicalCell L X s b T := by
  rw [closedPhysicalCell_eq_box L X s b T hX hs hb]
  exact cornerTuple_mem_box _ _ hne ε

/-- The common ordering in BNP1 is the literal inputOrdering S T of an
actual higher BGE1 cell. Its adjacency is a conclusion. The cell premise
is pointwise and in particular holds for every generated corner above. -/
theorem actual_promoted_chart_adjacent {m q : ℕ} (L : ℝ)
    (x y : Fin (m+q) → ℝ) (hx : StrictAnti x) (S T : PlacementSubset m q)
    (a t : Fin (m+q)) (ht : t ∈ S.1) (ha : a ∈ S.1.erase t) (b : Bool)
    (hd : physicalDomain L x (S.1.erase t) y b) (he : y a = x t)
    (hcell : (fun i => promoteTuple x y t (S.1.orderEmbOfFin S.2 i)) ∈
      BetheChartFiberSteps.closedPhysicalCell L (fun i => x (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b T) :
    if b then (inputOrdering S T a).val = (inputOrdering S T t).val+1
      else (inputOrdering S T t).val = (inputOrdering S T a).val+1 := by
  have hins : insert t (S.1.erase t) = S.1 := Finset.insert_erase ht
  have hs : Antitone (physicalInput x y (S.1.erase t) ∘ (inputOrdering S T).symm) := by
    rw [← physicalInput_promote x y (S.1.erase t) t (Finset.notMem_erase _ _), hins,
      physicalInput_inputOrdering]
    exact hcell.2.1
  exact promoted_chart_adjacent L x y hx (S.1.erase t) a t b hd ha
    (Finset.notMem_erase _ _) he (inputOrdering S T) hs
    (by simpa only [hins] using inputOrdering_orderedBlocks S T)

/-- The literal sourceRoots local balance at an actual BGE1 higher cell,
with all common-input rank adjacency derived. This remains a local identity:
no assertion about the sum over all corner or exterior labels is supplied. -/
theorem source_actual_promoted_chart_balance {m q : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (m+q) → ℤ} (hn : Antitone n)
    (x y : Fin (m+q) → ℝ) (hx : StrictAnti x) (S T : PlacementSubset m q)
    (a t : Fin (m+q)) (ht : t ∈ S.1) (ha : a ∈ S.1.erase t) (b : Bool)
    (hd : physicalDomain L x (S.1.erase t) y b) (he : y a = x t)
    (hcell : (fun i => promoteTuple x y t (S.1.orderEmbOfFin S.2 i)) ∈
      BetheChartFiberSteps.closedPhysicalCell L (fun i => x (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b T)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (ε : Fin (m+q) → Bool) (hea : ε a = b) (het : ε t = !b) :
    let A := S.1.erase t
    let π := inputOrdering S T
    let r := BetheSmooth.sourceRoots L n c
    let w := physicalInput x y A ∘ π.symm
    let P := fun D => BetheInternalFaces.primitive c r w z (integratedRanks π D)
    let phase := Complex.exp (Complex.I*z*(physicalOffset L x y A b : ℂ))
    (c : ℂ)^A.card * phase * physicalOrientation (A.erase a) ε *
        (if b then P A - P (insert t (A.erase a))
          else P (insert t (A.erase a)) - P A) +
      (c : ℂ)^(A.card+1) * phase * physicalOrientation (insert t A) ε *
        P (insert t A) = 0 := by
  exact source_promoted_face_balance hL hc hn x y (S.1.erase t) a t ha
    (Finset.notMem_erase _ _) he (inputOrdering S T) b
    (actual_promoted_chart_adjacent L x y hx S T a t ht ha b hd he hcell) z hz ε hea het

end QuantumNLS.BetheInputAdjacency

#print axioms QuantumNLS.BetheInputAdjacency.inputOrdering
#print axioms QuantumNLS.BetheInputAdjacency.physicalInput_inputOrdering
#print axioms QuantumNLS.BetheInputAdjacency.collision_internalGap
#print axioms QuantumNLS.BetheInputAdjacency.collision_isolated
#print axioms QuantumNLS.BetheInputAdjacency.isolated_pair_adjacent
#print axioms QuantumNLS.BetheInputAdjacency.mixed_collision_adjacent
#print axioms QuantumNLS.BetheInputAdjacency.orderedBlocks
#print axioms QuantumNLS.BetheInputAdjacency.inputOrdering_selected
#print axioms QuantumNLS.BetheInputAdjacency.inputOrdering_spectator
#print axioms QuantumNLS.BetheInputAdjacency.inputOrdering_orderedBlocks
#print axioms QuantumNLS.BetheInputAdjacency.chartOrderingEquiv
#print axioms QuantumNLS.BetheInputAdjacency.sorted_rank_lt
#print axioms QuantumNLS.BetheInputAdjacency.orderedBlocks_demote
#print axioms QuantumNLS.BetheInputAdjacency.orderedBlocks_promote
#print axioms QuantumNLS.BetheInputAdjacency.promoted_chart_adjacent
#print axioms QuantumNLS.BetheInputAdjacency.incident_ordering_iff
#print axioms QuantumNLS.BetheInputAdjacency.incidentOrderingEquiv
#print axioms QuantumNLS.BetheInputAdjacency.source_promoted_face_balance_of_chart
#print axioms QuantumNLS.BetheInputAdjacency.promoted_chart_domains_iff
#print axioms QuantumNLS.BetheInputAdjacency.generated_corner_mem_cell
#print axioms QuantumNLS.BetheInputAdjacency.actual_promoted_chart_adjacent
#print axioms QuantumNLS.BetheInputAdjacency.source_actual_promoted_chart_balance

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheInputAdjacency.chartOrderingEquiv,
    ``QuantumNLS.BetheInputAdjacency.incidentOrderingEquiv,
    ``QuantumNLS.BetheInputAdjacency.promoted_chart_domains_iff,
    ``QuantumNLS.BetheInputAdjacency.generated_corner_mem_cell,
    ``QuantumNLS.BetheInputAdjacency.actual_promoted_chart_adjacent,
    ``QuantumNLS.BetheInputAdjacency.source_promoted_face_balance_of_chart,
    ``QuantumNLS.BetheInputAdjacency.source_actual_promoted_chart_balance,
    ``QuantumNLS.BetheGeneratedEndpoints.source_transferTerm_corners_ae]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[
    ``QuantumNLS.BetheInputAdjacency.collision_internalGap,
    ``QuantumNLS.BetheInputAdjacency.collision_isolated,
    ``QuantumNLS.BetheInputAdjacency.mixed_collision_adjacent,
    ``QuantumNLS.BetheInputAdjacency.physicalInput_inputOrdering,
    ``QuantumNLS.BetheInputAdjacency.orderedBlocks_promote,
    ``QuantumNLS.BetheInputAdjacency.orderedBlocks_demote,
    ``QuantumNLS.BetheInputAdjacency.promoted_chart_adjacent,
    ``QuantumNLS.BetheNeighborPromotion.source_promoted_face_balance,
    ``QuantumNLS.BetheNeighborPromotion.physicalDomain_promote_iff,
    ``QuantumNLS.BetheGeneratedEndpoints.closedPhysicalCell_eq_box,
    ``QuantumNLS.BetheInternalFaces.source_primitive_internal_face,
    ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
    ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "Input adjacency aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Input adjacency aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Input adjacency aggregate audit PASS: {seen.size} transitive constants across separate roots. Actual input-chart representation, isolated mixed collision and derived adjacency, fixed-tuple oriented chart inverse, pointwise promoted sorted domains, and actual-cell local positive-c source balance. The BGE1 physical corner action is a separate root. Complete generated corner-label transport/global cancellation/eigenrelation remain OPEN."

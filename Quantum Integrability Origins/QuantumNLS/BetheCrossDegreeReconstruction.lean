import QuantumNLS.BetheSeamReconstruction

/-! Actual all-degree reconstruction from physical output subsets. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheCrossDegreeReconstruction
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport BetheGeneratedLabels BetheSeamProfiles
open BetheSeamReconstruction
attribute [local instance] Classical.propDecidable

/-- The original output subset, transported to the fixed ambient labels. -/
def outputSet {N : ℕ} (l : RawLabel N) : Finset (Fin N) :=
  l.2.1.1.map (ambient l.1).toEmbedding

/-- Rank permutation in the original ambient labels. -/
def ordering {N : ℕ} (l : RawLabel N) : Equiv.Perm (Fin N) :=
  (ambient l.1).symm.trans ((inputOrdering l.2.1 l.2.2.1).trans (ambient l.1))

/-- Physical Booleans, canonically false away from the output subset. -/
def booleans {N : ℕ} (l : RawLabel N) : Fin N → Bool :=
  branchExtension l.2.1 l.2.2 ∘ (ambient l.1).symm

/-- Cardinality is the literal degree of the original summand. -/
theorem outputSet_card {N : ℕ} (l : RawLabel N) : (outputSet l).card = l.1.val := by
  simp only [outputSet,Finset.card_map,l.2.1.2]

/-- Change only the finite ambient type. This transports all rectangle,
chart and endpoint constraints together, including at coincidences. -/
theorem cell_transport {M N : ℕ} (h : M = N) (L : ℝ) (x y : Fin N → ℝ)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N)) (b : Bool) :
    physicalCell L (x ∘ finCongr h) (A.map (finCongr h).symm.toEmbedding)
      ((finCongr h).trans (π.trans (finCongr h).symm)) b (y ∘ finCongr h) ↔
      physicalCell L x A π b y := by
  subst N
  simp

theorem orderedBlocks_transport {M N : ℕ} (h : M = N)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N)) :
    orderedBlocks (A.map (finCongr h).symm.toEmbedding)
      ((finCongr h).trans (π.trans (finCongr h).symm)) ↔ orderedBlocks A π := by
  subst N
  simp

theorem corner_transport {M N : ℕ} (h : M = N) (L : ℝ) (x : Fin N → ℝ)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N)) (b : Bool) (ε : Fin N → Bool) :
    physicalCorner L (x ∘ finCongr h) (A.map (finCongr h).symm.toEmbedding)
      ((finCongr h).trans (π.trans (finCongr h).symm)) b (ε ∘ finCongr h) =
      physicalCorner L x A π b ε ∘ finCongr h := by
  subst N
  simp

/-- Canonical degree of an arbitrary physical output subset. -/
def degree {N : ℕ} (A : Finset (Fin N)) : Fin (N+1) :=
  ⟨A.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ A)⟩

/-- Output chart in the exact split used by RawLabel. -/
def outputChart {N : ℕ} (A : Finset (Fin N)) :
    PlacementSubset (degree A).val (N-(degree A).val) :=
  ⟨A.map (ambient (degree A)).symm.toEmbedding, by simp [degree]⟩

/-- Reconstruct an original label at its own cardinal degree. No
independently chosen subset, rank, branch or Boolean quotient is used. -/
def reconstruct {N : ℕ} (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (hp : orderedBlocks A π) (b : Bool) (ε : Fin N → Bool) : RawLabel N :=
  ⟨degree A, outputChart A,
    branchOfOrdering (outputChart A)
      ((ambient (degree A)).trans (π.trans (ambient (degree A)).symm))
      ((orderedBlocks_transport _ A π).mpr hp) b (ε ∘ ambient (degree A))⟩

theorem reconstruct_branch {N : ℕ} (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (hp : orderedBlocks A π) (b : Bool) (ε : Fin N → Bool) :
    (reconstruct A π hp b ε).2.2.2.1 = b := rfl

theorem reconstruct_outputSet {N : ℕ} (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (hp : orderedBlocks A π) (b : Bool) (ε : Fin N → Bool) :
    outputSet (reconstruct A π hp b ε) = A := by
  simp [outputSet,reconstruct,outputChart,Finset.map_map]

theorem reconstruct_ordering {N : ℕ} (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (hp : orderedBlocks A π) (b : Bool) (ε : Fin N → Bool) :
    ordering (reconstruct A π hp b ε) = π := by
  dsimp only [ordering,reconstruct,branchOfOrdering]
  erw [chartOfOrdering_ordering]
  ext k
  simp

theorem reconstruct_admitted {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N)) (hp : orderedBlocks A π)
    (b : Bool) (ε : Fin N → Bool) (hy : physicalCell L x A π b y) :
    admitted L x (reconstruct A π hp b ε) := by
  have hx' : StrictAnti (x ∘ ambient (degree A)) := fun _ _ h => hx h
  exact branchOfOrdering_admitted L (x ∘ ambient (degree A))
    (y ∘ ambient (degree A)) hx' (fun k => hb _) (outputChart A) _ _ b _
    ((cell_transport _ L x y A π b).mpr hy)

theorem reconstruct_input {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N)) (hp : orderedBlocks A π)
    (b : Bool) (ε : Fin N → Bool) (hy : physicalCell L x A π b y) :
    fullInput L x (reconstruct A π hp b ε) = physicalCorner L x A π b ε := by
  have hx' : StrictAnti (x ∘ ambient (degree A)) := fun _ _ h => hx h
  have he := branchOfOrdering_input L (x ∘ ambient (degree A))
    (y ∘ ambient (degree A)) hx' (fun k => hb _) (outputChart A) _ ((orderedBlocks_transport _ A π).mpr hp) b
    (ε ∘ ambient (degree A)) ((cell_transport _ L x y A π b).mpr hy)
  have he' := he.trans (corner_transport _ L x A π b ε)

  change branchInput L (x ∘ ambient (degree A)) (outputChart A) _ ∘
    (ambient (degree A)).symm = _
  erw [he']
  funext k
  simp [ambient]

/-- Canonical extension has no spectator Boolean freedom. -/
theorem branchExtension_reconstructed {m q : ℕ} (S : PlacementSubset m q)
    (π : Equiv.Perm (Fin (m+q))) (hp : orderedBlocks S.1 π)
    (b : Bool) (ε : Fin (m+q) → Bool) (k : Fin (m+q)) :
    branchExtension S (branchOfOrdering S π hp b ε) k =
      if k ∈ S.1 then ε k else false := by
  obtain ⟨a,rfl⟩ := (mergePermutation S).surjective k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) a
  · rw [mergePermutation_selected,branchExtension_selected]
    simp [branchOfOrdering,S.1.orderEmbOfFin_mem S.2 i]
  · simp only [branchExtension,Function.comp_apply,Equiv.symm_apply_apply,
      Fin.addCases_right]
    rw [mergePermutation_spectator]
    simp [Finset.mem_compl.mp (S.1ᶜ.orderEmbOfFin_mem (complement_card S) j)]

theorem reconstruct_booleans {N : ℕ} (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (hp : orderedBlocks A π) (b : Bool) (ε : Fin N → Bool)
    (k : Fin N) :
    booleans (reconstruct A π hp b ε) k = if k ∈ A then ε k else false := by
  change branchExtension (outputChart A) (branchOfOrdering _ _ _ b
    (ε ∘ ambient (degree A))) ((ambient (degree A)).symm k) = _
  erw [branchExtension_reconstructed]
  simp [outputChart]

theorem booleans_off {N : ℕ} (l : RawLabel N) (k : Fin N)
    (hk : k ∉ outputSet l) : booleans l k = false := by
  let S := l.2.1
  let u := l.2.2
  have hr := branchOfOrdering_inverse S u
  have h := branchExtension_reconstructed S (inputOrdering S u.1)
    (inputOrdering_orderedBlocks S u.1) u.2.1 (branchExtension S u)
    ((ambient l.1).symm k)
  rw [hr] at h
  have hk' : (ambient l.1).symm k ∉ S.1 := by
    simpa [outputSet,S] using hk
  simpa only [hk',ite_false,booleans,Function.comp_apply] using h

/-- These data retain every original RawLabel, even at collapsed corners.
Input values alone would lose its distinct Boolean labels. -/
theorem rawLabel_unique {N : ℕ} (l u : RawLabel N)
    (hA : outputSet l = outputSet u) (hπ : ordering l = ordering u)
    (hb : l.2.2.2.1 = u.2.2.2.1) (hε : booleans l = booleans u) : l = u := by
  have hd : l.1 = u.1 := Fin.ext ((outputSet_card l).symm.trans
    ((congrArg Finset.card hA).trans (outputSet_card u)))
  rcases l with ⟨d,S,v⟩
  rcases u with ⟨e,T,w⟩
  dsimp only at hd
  subst e
  have hS : S = T := by
    apply Subtype.ext
    have h := congrArg (fun A => A.map (ambient d).symm.toEmbedding) hA
    simpa [outputSet,Finset.map_map] using h
  subst T
  have hc : v.1 = w.1 := by
    apply (chartOrderingEquiv S).injective
    have hco : inputOrdering S v.1 = inputOrdering S w.1 := by
      ext k
      have h := congrArg (fun p : Equiv.Perm (Fin N) =>
        (ambient d).symm (p (ambient d k))) hπ
      exact congrArg Fin.val (by simpa [ordering] using h)
    exact Subtype.ext hco
  have he : v.2.2 = w.2.2 := by
    funext i
    have h := congrFun hε (ambient d (S.1.orderEmbOfFin S.2 i))
    simpa [booleans,branchExtension_selected] using h
  have hv : v = w := Prod.ext hc (Prod.ext hb he)
  subst w
  rfl

theorem outputSet_pullback {N : ℕ} (l : RawLabel N) :
    (outputSet l).map (ambient l.1).symm.toEmbedding = l.2.1.1 := by
  simp [outputSet,Finset.map_map]

theorem ordering_pullback {N : ℕ} (l : RawLabel N) :
    (ambient l.1).trans ((ordering l).trans (ambient l.1).symm) =
      inputOrdering l.2.1 l.2.2.1 := by
  ext k
  simp [ordering]

theorem outputSet_orderedBlocks {N : ℕ} (l : RawLabel N) :
    orderedBlocks (outputSet l) (ordering l) := by
  apply (orderedBlocks_transport (M := l.1.val+(N-l.1.val)) (by omega)
    (outputSet l) (ordering l)).mp
  change orderedBlocks ((outputSet l).map (ambient l.1).symm.toEmbedding)
    ((ambient l.1).trans ((ordering l).trans (ambient l.1).symm))
  rw [outputSet_pullback,ordering_pullback]
  exact inputOrdering_orderedBlocks l.2.1 l.2.2.1

/-- Every admitted original label is a supported physical corner in its
own original ambient labels, including degree zero and degree N. -/
theorem label_cell {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) :
    physicalCell L x (outputSet l) (ordering l) l.2.2.2.1 (fullInput L x l) := by
  apply (cell_transport (M := l.1.val+(N-l.1.val)) (by omega) L x (fullInput L x l) (outputSet l)
    (ordering l) l.2.2.2.1).mp
  have hx' : StrictAnti (x ∘ ambient l.1) := fun _ _ h => hx h
  have h := admitted_corner_cell L (x ∘ ambient l.1) hx' (fun k => hb _)
    l.2.1 l.2.2 hl
  change physicalCell L (x ∘ ambient l.1) l.2.1.1
    (inputOrdering l.2.1 l.2.2.1) l.2.2.2.1 (branchInput L (x ∘ ambient l.1) l.2.1 l.2.2) at h
  have hf : fullInput L x l = branchInput L (x ∘ ambient l.1) l.2.1 l.2.2 ∘
    (ambient l.1).symm := rfl
  change physicalCell L (x ∘ ambient l.1)
    ((outputSet l).map (ambient l.1).symm.toEmbedding)
    ((ambient l.1).trans ((ordering l).trans (ambient l.1).symm))
    l.2.2.2.1 (fullInput L x l ∘ ambient l.1)
  rw [outputSet_pullback,ordering_pullback,hf]
  simpa only [Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using h

/-- Exact inverse in the original sum's label space. -/
theorem reconstruct_inverse {N : ℕ} (l : RawLabel N) :
    reconstruct (outputSet l) (ordering l) (outputSet_orderedBlocks l)
      l.2.2.2.1 (booleans l) = l := by
  apply rawLabel_unique
  · exact reconstruct_outputSet _ _ _ _ _
  · exact reconstruct_ordering _ _ _ _ _
  · rfl
  · funext k
    rw [reconstruct_booleans]
    by_cases hk : k ∈ outputSet l
    · simp [hk]
    · simp [hk,booleans_off l k hk]

theorem label_corner {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) :
    fullInput L x l = physicalCorner L x (outputSet l) (ordering l)
      l.2.2.2.1 (booleans l) := by
  have h := reconstruct_input L x (fullInput L x l) hx hb _ _
    (outputSet_orderedBlocks l) l.2.2.2.1 (booleans l) (label_cell L x hx hb l hl)
  rw [reconstruct_inverse] at h
  exact h

/-- Promotion is an actual RawLabel at degree card(A)+1. -/
def promoteLabel {N : ℕ} (l : RawLabel N) (t : Fin N)
    (hp : orderedBlocks (insert t (outputSet l)) (ordering l)) : RawLabel N :=
  reconstruct (insert t (outputSet l)) (ordering l) hp l.2.2.2.1
    (Function.update (booleans l) t (!l.2.2.2.1))

/-- Deletion reconstructs its own exact lower degree and chart. -/
def demoteLabel {N : ℕ} (l : RawLabel N) (t : Fin N)
    (hp : orderedBlocks ((outputSet l).erase t) (ordering l)) : RawLabel N :=
  reconstruct ((outputSet l).erase t) (ordering l) hp l.2.2.2.1 (booleans l)

theorem promoteLabel_data {N : ℕ} (l : RawLabel N) (t : Fin N)
    (hp : orderedBlocks (insert t (outputSet l)) (ordering l)) :
    outputSet (promoteLabel l t hp) = insert t (outputSet l) ∧
    ordering (promoteLabel l t hp) = ordering l ∧
    (promoteLabel l t hp).2.2.2.1 = l.2.2.2.1 :=
  ⟨reconstruct_outputSet _ _ _ _ _,reconstruct_ordering _ _ _ _ _,rfl⟩

theorem demoteLabel_data {N : ℕ} (l : RawLabel N) (t : Fin N)
    (hp : orderedBlocks ((outputSet l).erase t) (ordering l)) :
    outputSet (demoteLabel l t hp) = (outputSet l).erase t ∧
    ordering (demoteLabel l t hp) = ordering l ∧
    (demoteLabel l t hp).2.2.2.1 = l.2.2.2.1 :=
  ⟨reconstruct_outputSet _ _ _ _ _,reconstruct_ordering _ _ _ _ _,rfl⟩

/-- The maps change the literal degree exactly once. -/
theorem promoteLabel_degree {N : ℕ} (l : RawLabel N) (t : Fin N)
    (ht : t ∉ outputSet l)
    (hp : orderedBlocks (insert t (outputSet l)) (ordering l)) :
    (promoteLabel l t hp).1.val = l.1.val+1 := by
  rw [← outputSet_card,(promoteLabel_data _ _ _).1,Finset.card_insert_of_notMem ht,outputSet_card]

/-- The original lower label is recovered, with all its Boolean labels.
This algebraic inverse also holds at collapsed intervals. -/
theorem demote_promote_inverse {N : ℕ} (l : RawLabel N) (t : Fin N)
    (ht : t ∉ outputSet l)
    (hp : orderedBlocks (insert t (outputSet l)) (ordering l))
    (hq : orderedBlocks ((outputSet (promoteLabel l t hp)).erase t)
      (ordering (promoteLabel l t hp))) :
    demoteLabel (promoteLabel l t hp) t hq = l := by
  apply rawLabel_unique
  · rw [(demoteLabel_data _ _ _).1,(promoteLabel_data _ _ _).1,
      Finset.erase_insert ht]
  · rw [(demoteLabel_data _ _ _).2.1,(promoteLabel_data _ _ _).2.1]
  · rfl
  · funext k
    simp only [demoteLabel,promoteLabel,reconstruct_booleans,reconstruct_outputSet]
    by_cases hk : k ∈ outputSet l
    · have hkt : k ≠ t := fun h => ht (h ▸ hk)
      simp [hk,hkt]
    · simp [hk,Finset.erase_insert ht,booleans_off l k hk]

/-- The original higher label is recovered when its marked Boolean is
its derived pinned endpoint label. No label multiplicity is suppressed. -/
theorem promote_demote_inverse {N : ℕ} (l : RawLabel N) (t : Fin N)
    (ht : t ∈ outputSet l) (he : booleans l t = !l.2.2.2.1)
    (hp : orderedBlocks ((outputSet l).erase t) (ordering l))
    (hq : orderedBlocks (insert t (outputSet (demoteLabel l t hp)))
      (ordering (demoteLabel l t hp))) :
    promoteLabel (demoteLabel l t hp) t hq = l := by
  apply rawLabel_unique
  · rw [(promoteLabel_data _ _ _).1,(demoteLabel_data _ _ _).1,
      Finset.insert_erase ht]
  · rw [(promoteLabel_data _ _ _).2.1,(demoteLabel_data _ _ _).2.1]
  · rfl
  · funext k
    simp only [promoteLabel,reconstruct_booleans,demoteLabel,
      reconstruct_booleans,reconstruct_outputSet]
    have heps : booleans (reconstruct ((outputSet l).erase t) (ordering l) hp
      l.2.2.2.1 (booleans l)) =
        fun j => if j ∈ (outputSet l).erase t then booleans l j else false :=
      funext (reconstruct_booleans _ _ _ _ _)
    rw [heps,reconstruct_branch]
    change (if k ∈ insert t ((outputSet l).erase t) then
      Function.update (fun j => if j ∈ (outputSet l).erase t then booleans l j else false)
        t (!l.2.2.2.1) k else false) = booleans l k
    by_cases hkt : k = t
    · subst k
      simp [ht,he]
    · by_cases hk : k ∈ outputSet l
      · simp [hk,hkt]
      · simp [hk,hkt,booleans_off l k hk]

/-- The full tuple ignores extension values off the selected set. -/
theorem corner_update_spectator {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N)) (b : Bool) (ε : Fin N → Bool)
    (t : Fin N) (ht : t ∉ A) (v : Bool) :
    physicalCorner L x A π b (Function.update ε t v) = physicalCorner L x A π b ε := by
  funext k
  by_cases hk : k ∈ A
  · have hkt : k ≠ t := fun h => ht (h ▸ hk)
    simp [physicalCorner,hk,hkt]
  · simp [physicalCorner,hk]

/-- Branch incidence is derived from the actual original noncollapsed
label, rather than assumed in its promotion. -/
theorem label_mixed_incident_iff {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (a t : Fin N)
    (ha : a ∈ outputSet l) (ht : t ∉ outputSet l)
    (he : fullInput L x l a = x t)
    (hn : physicalLo x (outputSet l) (ordering l) l.2.2.2.1 a <
      physicalHi L x (outputSet l) (ordering l) l.2.2.2.1 a) :
    orderedBlocks (insert t (outputSet l)) (ordering l) ↔
      booleans l a = l.2.2.2.1 := by
  have hy := label_cell L x hx hb l hl
  rw [label_corner L x hx hb l hl] at hy he
  exact mixed_corner_incident_iff L x hx _ _ (outputSet_orderedBlocks l) _ _
    hy a t ha ht he hn

/-- Actual promoted labels are admitted and preserve the whole original
input and hence every simultaneous seam and the chosen mark. -/
theorem promoteLabel_supported {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (a t : Fin N)
    (ha : a ∈ outputSet l) (ht : t ∉ outputSet l)
    (he : fullInput L x l a = x t) (hε : booleans l a = l.2.2.2.1)
    (hp : orderedBlocks (insert t (outputSet l)) (ordering l)) :
    admitted L x (promoteLabel l t hp) ∧
    fullInput L x (promoteLabel l t hp) = fullInput L x l ∧
    labelMark L x (promoteLabel l t hp) = labelMark L x l := by
  have hb' : ∀ k, x k ∈ Icc 0 L := fun k => ⟨(hb k).1.le,(hb k).2.le⟩
  have hy := label_cell L x hx hb l hl
  have hg := collision_internalGap L x _ hx _ a t _ hy.1 ha ht he
  have hy' := (promoted_chart_domains_iff L x _ hx.antitone hb' _ a t _ hg he
    (ordering l)).mpr hy
  have hadm := reconstruct_admitted L x _ hx hb _ _ hp _
    (Function.update (booleans l) t (!l.2.2.2.1)) hy'
  have hi := reconstruct_input L x _ hx hb _ _ hp _
    (Function.update (booleans l) t (!l.2.2.2.1)) hy'
  have hat : a ≠ t := fun h => ht (h ▸ ha)
  have hc := physicalCorner_promote L x _ hx hb' _ a t _ hg he (ordering l) hp hy
    (Function.update (booleans l) t (!l.2.2.2.1))
    (by simpa [hat] using hε) (by simp)
  have hinput : fullInput L x (promoteLabel l t hp) = fullInput L x l := by
    exact hi.trans (hc.symm.trans ((corner_update_spectator L x _ _ _ _ t ht _).trans
      (label_corner L x hx hb l hl).symm))
  exact ⟨hadm,hinput,congrArg (fun v => chooseSeam (seams v)) hinput⟩

/-- Actual higher selected/selected seams determine both marked Booleans
from their original noncollapsed intervals. -/
theorem label_selected_orientations {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (i j : Fin N)
    (hi : i ∈ outputSet l) (hj : j ∈ outputSet l) (hij : i < j)
    (he : fullInput L x l i = fullInput L x l j)
    (hni : physicalLo x (outputSet l) (ordering l) l.2.2.2.1 i <
      physicalHi L x (outputSet l) (ordering l) l.2.2.2.1 i)
    (hnj : physicalLo x (outputSet l) (ordering l) l.2.2.2.1 j <
      physicalHi L x (outputSet l) (ordering l) l.2.2.2.1 j) :
    booleans l i = false ∧ booleans l j = true := by
  have hy := label_cell L x hx hb l hl
  rw [label_corner L x hx hb l hl] at hy he
  exact selected_corner_orientations L x hx _ _ (outputSet_orderedBlocks l) _ _
    hy i j hi hj hij he hni hnj

/-- Pinned higher demotion constructs an actual admitted original label;
its lower chart is derived from the higher support. -/
theorem demoteLabel_supported {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (a t : Fin N)
    (hg : promotedGap (outputSet l) a t l.2.2.2.1)
    (ha : fullInput L x l a = x t) (ht : fullInput L x l t = x t)
    (hεa : booleans l a = l.2.2.2.1) (hεt : booleans l t = !l.2.2.2.1) :
    ∃ hp : orderedBlocks ((outputSet l).erase t) (ordering l),
      admitted L x (demoteLabel l t hp) ∧
      fullInput L x (demoteLabel l t hp) = fullInput L x l ∧
      labelMark L x (demoteLabel l t hp) = labelMark L x l := by
  have hb' : ∀ k, x k ∈ Icc 0 L := fun k => ⟨(hb k).1.le,(hb k).2.le⟩
  have hy := label_cell L x hx hb l hl
  rw [label_corner L x hx hb l hl] at hy ha ht
  have hd := pinned_corner_demote L x hx hb' _ _ (outputSet_orderedBlocks l)
    _ _ hy a t hg ha ht hεa hεt
  refine ⟨hd.1,reconstruct_admitted L x _ hx hb _ _ hd.1 _ _ hd.2.1,?_⟩
  have hinput : fullInput L x (demoteLabel l t hd.1) = fullInput L x l :=
    (reconstruct_input L x _ hx hb _ _ hd.1 _ _ hd.2.1).trans
      (hd.2.2.trans (label_corner L x hx hb l hl).symm)
  exact ⟨hinput,congrArg (fun v => chooseSeam (seams v)) hinput⟩

/-- Canonical physical data retain the entire Boolean label; values off
its output subset are fixed extension values, not additional labels. -/
abbrev PhysicalLabel (N : ℕ) :=
  {p : Finset (Fin N) × (Equiv.Perm (Fin N) × (Bool × (Fin N → Bool))) //
    orderedBlocks p.1 p.2.1 ∧ ∀ k, k ∉ p.1 → p.2.2.2 k = false}

/-- Exact all-degree equivalence before imposing support. Empty boxes and
collapsed Boolean labels have not been discarded or identified. -/
def physicalLabelEquiv (N : ℕ) : RawLabel N ≃ PhysicalLabel N where
  toFun l := ⟨(outputSet l,ordering l,l.2.2.2.1,booleans l),
    outputSet_orderedBlocks l,booleans_off l⟩
  invFun p := reconstruct p.1.1 p.1.2.1 p.2.1 p.1.2.2.1 p.1.2.2.2
  left_inv l := reconstruct_inverse l
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact reconstruct_outputSet _ _ _ _ _
    apply Prod.ext
    · exact reconstruct_ordering _ _ _ _ _
    apply Prod.ext
    · rfl
    funext k
    change booleans (reconstruct p.1.1 p.1.2.1 p.2.1 p.1.2.2.1 p.1.2.2.2) k = p.1.2.2.2 k
    rw [reconstruct_booleans]
    by_cases hk : k ∈ p.1.1
    · simp [hk]
    · simp [hk,p.2.2 k hk]

/-- The exchange chart is derived from every actual supported mixed seam,
including when unrelated seams occur simultaneously. -/
theorem label_exchanged_chart {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (a t : Fin N)
    (ha : a ∈ outputSet l) (ht : t ∉ outputSet l)
    (he : fullInput L x l a = x t) :
    orderedBlocks (outputSet l) (exchangedOrdering (ordering l) a t) := by
  have hy := label_cell L x hx hb l hl
  exact exchangedOrdering_orderedBlocks _ _ a t ha ht (outputSet_orderedBlocks l)
    (mixed_collision_adjacent L x _ hx _ a t _ hy.1 ha ht he _ hy.2).symm

/-- Every original noncollapsed higher seam yields an admitted lower
RawLabel at the erased subset. Pinning, branch orientation and the lower
chart are all derived from the original label, rather than supplied as
independent geometric hypotheses. -/
theorem selected_seam_actual_demote {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (i j : Fin N)
    (hi : i ∈ outputSet l) (hj : j ∈ outputSet l) (hij : i < j)
    (he : fullInput L x l i = fullInput L x l j)
    (hni : physicalLo x (outputSet l) (ordering l) l.2.2.2.1 i <
      physicalHi L x (outputSet l) (ordering l) l.2.2.2.1 i)
    (hnj : physicalLo x (outputSet l) (ordering l) l.2.2.2.1 j <
      physicalHi L x (outputSet l) (ordering l) l.2.2.2.1 j) :
    if l.2.2.2.1 then
      ∃ hp : orderedBlocks ((outputSet l).erase i) (ordering l),
        admitted L x (demoteLabel l i hp) ∧
        fullInput L x (demoteLabel l i hp) = fullInput L x l ∧
        labelMark L x (demoteLabel l i hp) = labelMark L x l
    else
      ∃ hp : orderedBlocks ((outputSet l).erase j) (ordering l),
        admitted L x (demoteLabel l j hp) ∧
        fullInput L x (demoteLabel l j hp) = fullInput L x l ∧
        labelMark L x (demoteLabel l j hp) = labelMark L x l := by
  have hc := label_cell L x hx hb l hl
  have ho := label_selected_orientations L x hx hb l hl i j hi hj hij he hni hnj
  have hg := selected_collision_gap L x _ hx _ l.2.2.2.1 hc.1 i j hi hj hij he
  cases hbranch : l.2.2.2.1
  · simp only [hbranch,Bool.false_eq_true,ite_false] at hg ⊢
    exact demoteLabel_supported L x hx hb l hl i j (by simpa [hbranch] using hg.1)
      hg.2.1 hg.2.2 (by simpa [hbranch] using ho.1) (by simpa [hbranch] using ho.2)
  · simp only [hbranch,ite_true] at hg ⊢
    exact demoteLabel_supported L x hx hb l hl j i (by simpa [hbranch] using hg.1)
      hg.2.1 hg.2.2 (by simpa [hbranch] using ho.2) (by simpa [hbranch] using ho.1)

end QuantumNLS.BetheCrossDegreeReconstruction


#print axioms QuantumNLS.BetheCrossDegreeReconstruction.outputSet
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.ordering
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.booleans
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.outputSet_card
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.cell_transport
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.orderedBlocks_transport
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.corner_transport
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.degree
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.outputChart
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.reconstruct
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_branch
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_outputSet
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_ordering
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_admitted
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_input
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.branchExtension_reconstructed
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_booleans
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.booleans_off
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.rawLabel_unique
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.outputSet_pullback
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.ordering_pullback
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.outputSet_orderedBlocks
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.label_cell
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_inverse
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.label_corner
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.promoteLabel
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.demoteLabel
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.promoteLabel_data
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.demoteLabel_data
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.promoteLabel_degree
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.demote_promote_inverse
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.promote_demote_inverse
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.corner_update_spectator
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.label_mixed_incident_iff
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.promoteLabel_supported
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.label_selected_orientations
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.demoteLabel_supported
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.PhysicalLabel
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.physicalLabelEquiv
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.label_exchanged_chart
#print axioms QuantumNLS.BetheCrossDegreeReconstruction.selected_seam_actual_demote
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheCrossDegreeReconstruction.outputSet,
    ``QuantumNLS.BetheCrossDegreeReconstruction.ordering,
    ``QuantumNLS.BetheCrossDegreeReconstruction.booleans,
    ``QuantumNLS.BetheCrossDegreeReconstruction.outputSet_card,
    ``QuantumNLS.BetheCrossDegreeReconstruction.cell_transport,
    ``QuantumNLS.BetheCrossDegreeReconstruction.orderedBlocks_transport,
    ``QuantumNLS.BetheCrossDegreeReconstruction.corner_transport,
    ``QuantumNLS.BetheCrossDegreeReconstruction.degree,
    ``QuantumNLS.BetheCrossDegreeReconstruction.outputChart,
    ``QuantumNLS.BetheCrossDegreeReconstruction.reconstruct,
    ``QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_branch,
    ``QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_outputSet,
    ``QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_ordering,
    ``QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_admitted,
    ``QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_input,
    ``QuantumNLS.BetheCrossDegreeReconstruction.branchExtension_reconstructed,
    ``QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_booleans,
    ``QuantumNLS.BetheCrossDegreeReconstruction.booleans_off,
    ``QuantumNLS.BetheCrossDegreeReconstruction.rawLabel_unique,
    ``QuantumNLS.BetheCrossDegreeReconstruction.outputSet_pullback,
    ``QuantumNLS.BetheCrossDegreeReconstruction.ordering_pullback,
    ``QuantumNLS.BetheCrossDegreeReconstruction.outputSet_orderedBlocks,
    ``QuantumNLS.BetheCrossDegreeReconstruction.label_cell,
    ``QuantumNLS.BetheCrossDegreeReconstruction.reconstruct_inverse,
    ``QuantumNLS.BetheCrossDegreeReconstruction.label_corner,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promoteLabel,
    ``QuantumNLS.BetheCrossDegreeReconstruction.demoteLabel,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promoteLabel_data,
    ``QuantumNLS.BetheCrossDegreeReconstruction.demoteLabel_data,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promoteLabel_degree,
    ``QuantumNLS.BetheCrossDegreeReconstruction.demote_promote_inverse,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promote_demote_inverse,
    ``QuantumNLS.BetheCrossDegreeReconstruction.corner_update_spectator,
    ``QuantumNLS.BetheCrossDegreeReconstruction.label_mixed_incident_iff,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promoteLabel_supported,
    ``QuantumNLS.BetheCrossDegreeReconstruction.label_selected_orientations,
    ``QuantumNLS.BetheCrossDegreeReconstruction.demoteLabel_supported,
    ``QuantumNLS.BetheCrossDegreeReconstruction.PhysicalLabel,
    ``QuantumNLS.BetheCrossDegreeReconstruction.physicalLabelEquiv,
    ``QuantumNLS.BetheCrossDegreeReconstruction.label_exchanged_chart,
    ``QuantumNLS.BetheCrossDegreeReconstruction.selected_seam_actual_demote,
    ``QuantumNLS.BetheSeamProfiles.sum_marks_original,
    ``QuantumNLS.BetheSeamProfiles.source_chosen_corner_balance,
    ``QuantumNLS.BetheSeamProfiles.sum_collapsed_mark,
    ``QuantumNLS.BetheGeneratedLabels.source_transferTerm_labels_ae]
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
    ``QuantumNLS.BetheSeamProfiles.sum_marks_original,
    ``QuantumNLS.BetheSeamProfiles.sum_collapsed_mark,
    ``QuantumNLS.BetheSeamProfiles.source_chosen_corner_balance,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_promote,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_exchanged,
    ``QuantumNLS.BetheCornerTransport.source_generated_corner_balance,
    ``QuantumNLS.BetheGeneratedLabels.source_transferTerm_labels_ae,
    ``QuantumNLS.BetheInputAdjacency.chartOrderingEquiv,
    ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
    ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "Cross-degree reconstruction aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Cross-degree reconstruction aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Cross-degree reconstruction aggregate audit PASS: {seen.size} transitive constants across separate roots. Exact all-degree raw/physical label equivalence, supported actual promotion/demotion with literal inverses, full-input and chosen-mark preservation, and selected-seam original-label demotion. Frozen signed partition, collapsed cancellation and local triple balance audited separately. Exhaustive disjoint BCT1 triple partition, exterior survivors, global sums and spectral assembly remain OPEN."

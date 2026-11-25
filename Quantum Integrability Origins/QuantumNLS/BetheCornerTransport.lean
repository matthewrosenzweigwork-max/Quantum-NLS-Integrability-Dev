import QuantumNLS.BetheInputAdjacency

/-! Clipped endpoint transport in original physical labels. Candidate sets
use all original rectangle inequalities; no choice of a maximizing provenance
label is made when endpoint values coincide. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheCornerTransport
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheChartFiberSteps

def lowerValues {N : ℕ} (x : Fin N → ℝ) (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (b : Bool) (k : Fin N) : Finset ℝ :=
  insert (if b then x k else 0)
    (((A.filter (fun l => b = false ∧ k < l)).image x) ∪
      ((Aᶜ.filter (fun l => π k < π l)).image x))

def upperValues {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (b : Bool) (k : Fin N) : Finset ℝ :=
  insert (if b then L else x k)
    (((A.filter (fun l => b ∧ l < k)).image x) ∪
      ((Aᶜ.filter (fun l => π l < π k)).image x))

def physicalLo {N : ℕ} (x : Fin N → ℝ) (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (b : Bool) (k : Fin N) : ℝ :=
  (lowerValues x A π b k).max' ⟨_, Finset.mem_insert_self _ _⟩

def physicalHi {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (b : Bool) (k : Fin N) : ℝ :=
  (upperValues L x A π b k).min' ⟨_, Finset.mem_insert_self _ _⟩

theorem physicalLo_le_iff {N : ℕ} (x : Fin N → ℝ) (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (b : Bool) (k : Fin N) (v : ℝ) :
    physicalLo x A π b k ≤ v ↔
      (if b then x k else 0) ≤ v ∧
      (∀ l ∈ A, (b = false ∧ k < l) → x l ≤ v) ∧
      (∀ l ∉ A, π k < π l → x l ≤ v) := by
  simp only [physicalLo, Finset.max'_le_iff, lowerValues, Finset.forall_mem_insert,
    Finset.forall_mem_union, Finset.forall_mem_image, Finset.mem_filter,
    Finset.mem_compl, and_imp]

theorem le_physicalHi_iff {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N)) (b : Bool)
    (k : Fin N) (v : ℝ) :
    v ≤ physicalHi L x A π b k ↔
      v ≤ (if b then L else x k) ∧
      (∀ l ∈ A, (b = true ∧ l < k) → v ≤ x l) ∧
      (∀ l ∉ A, π l < π k → v ≤ x l) := by
  simp only [physicalHi, Finset.le_min'_iff, upperValues, Finset.forall_mem_insert,
    Finset.forall_mem_union, Finset.forall_mem_image, Finset.mem_filter,
    Finset.mem_compl, and_imp]

def physicalCell {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (b : Bool) (y : Fin N → ℝ) : Prop :=
  physicalDomain L x A y b ∧ Antitone (physicalInput x y A ∘ π.symm)

theorem selected_antitone {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (A : Finset (Fin N)) (b : Bool) (hd : physicalDomain L x A y b)
    (k l : Fin N) (hk : k ∈ A) (hl : l ∈ A) (hkl : k < l) : y l ≤ y k := by
  cases b
  · exact ((hd l hl).2.1).trans ((hd k hk).2.2 l hl hkl)
  · exact ((hd l hl).2.2 k hk hkl).trans (hd k hk).1

/-- All cell constraints are a product of intervals in the selected
physical labels. Moving/moving constraints follow from the rectangle. -/
theorem physicalCell_iff_box {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : Antitone x) (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (hp : orderedBlocks A π) (b : Bool) :
    physicalCell L x A π b y ↔
      ∀ k ∈ A, y k ∈ Icc (physicalLo x A π b k) (physicalHi L x A π b k) := by
  classical
  constructor
  · rintro ⟨hd, hs⟩ k hk
    have cross (i j : Fin N) (hij : π i < π j) :
        physicalInput x y A j ≤ physicalInput x y A i := by
      have h := hs hij.le
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h
    constructor
    · rw [physicalLo_le_iff]
      refine ⟨?_, ?_, ?_⟩
      · cases b
        · exact (hd k hk).1
        · exact (hd k hk).1
      · intro l hl h
        cases b
        · exact (hd k hk).2.2 l hl h.2
        · simp at h
      · intro l hl h
        simpa [physicalInput, hk, hl] using cross k l h
    · rw [le_physicalHi_iff]
      refine ⟨?_, ?_, ?_⟩
      · cases b
        · exact (hd k hk).2.1
        · exact (hd k hk).2.1
      · intro l hl h
        cases b
        · simp at h
        · exact (hd k hk).2.2 l hl h.2
      · intro l hl h
        simpa [physicalInput, hk, hl] using cross l k h
  · intro h
    have hl (k : Fin N) (hk : k ∈ A) := (physicalLo_le_iff x A π b k (y k)).mp (h k hk).1
    have hu (k : Fin N) (hk : k ∈ A) := (le_physicalHi_iff L x A π b k (y k)).mp (h k hk).2
    have hd : physicalDomain L x A y b := by
      intro k hk
      cases b
      · exact ⟨(hl k hk).1, (hu k hk).1, fun l hl' hkl => (hl k hk).2.1 l hl' ⟨rfl,hkl⟩⟩
      · exact ⟨(hl k hk).1, (hu k hk).1, fun l hl' hlk => (hu k hk).2.1 l hl' ⟨rfl,hlk⟩⟩
    refine ⟨hd, ?_⟩
    intro i j hij
    let k := π.symm i
    let l := π.symm j
    have hπ : π k ≤ π l := by simpa [k,l] using hij
    by_cases hkl : k = l
    · change physicalInput x y A l ≤ physicalInput x y A k
      rw [hkl]
    have hπ' : π k < π l := lt_of_le_of_ne hπ (fun h => hkl (π.injective h))
    change physicalInput x y A l ≤ physicalInput x y A k
    by_cases hk : k ∈ A <;> by_cases hh : l ∈ A
    · have horder : k < l := by
        by_contra hn
        have hrev := hp.1 l hh k hk (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hkl))
        exact (not_lt_of_gt hπ') hrev
      simpa [physicalInput, hk, hh] using selected_antitone L x y A b hd k l hk hh horder
    · simpa [physicalInput, hk, hh] using (hl k hk).2.2 l hh hπ'
    · simpa [physicalInput, hk, hh] using (hu l hh).2.2 k hk hπ'
    · have horder : k < l := by
        by_contra hn
        have hrev := hp.2 l hh k hk (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hkl))
        exact (not_lt_of_gt hπ') hrev
      simpa [physicalInput, hk, hh] using hx horder.le

/-- The entire selected-coordinate fiber, through any admitted point. -/
theorem physicalCell_update_iff {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : Antitone x) (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (hp : orderedBlocks A π) (b : Bool) (hy : physicalCell L x A π b y)
    (k : Fin N) (hk : k ∈ A) (v : ℝ) :
    physicalCell L x A π b (Function.update y k v) ↔
      v ∈ Icc (physicalLo x A π b k) (physicalHi L x A π b k) := by
  rw [physicalCell_iff_box L x _ hx A π hp b]
  have hy' := (physicalCell_iff_box L x y hx A π hp b).mp hy
  constructor
  · intro h
    simpa only [Function.update_self] using h k hk
  · intro h j hj
    by_cases he : j = k
    · subst j; simpa using h
    · simpa only [Function.update_of_ne he] using hy' j hj

theorem interval_endpoints_of_iff (lo hi lo' hi' v : ℝ)
    (hv : v ∈ Icc lo hi) (he : ∀ u, u ∈ Icc lo hi ↔ u ∈ Icc lo' hi') :
    lo = lo' ∧ hi = hi' := by
  have hv' := (he v).mp hv
  have h := hv.1.trans hv.2
  have h' := hv'.1.trans hv'.2
  exact ⟨le_antisymm ((he lo').mpr ⟨le_rfl,h'⟩).1 ((he lo).mp ⟨le_rfl,h⟩).1,
    le_antisymm ((he hi).mp ⟨h,le_rfl⟩).2 ((he hi').mpr ⟨h',le_rfl⟩).2⟩

/-- Equality of every unmarked lower and upper clipped endpoint, obtained
from complete fibers. It is valid through collapsed intervals and other
collisions; no generic-corner premise occurs. -/
theorem physical_endpoints_promote {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Icc 0 L)
    (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hg : internalGap A a t b) (he : y a = x t)
    (π : Equiv.Perm (Fin N)) (hp : orderedBlocks (insert t A) π)
    (hy : physicalCell L x A π b y) (k : Fin N) (hk : k ∈ A) (hka : k ≠ a) :
    physicalLo x A π b k = physicalLo x (insert t A) π b k ∧
      physicalHi L x A π b k = physicalHi L x (insert t A) π b k := by
  classical
  have hkt : k ≠ t := fun h => hg.2.1 (h ▸ hk)
  have hp' := orderedBlocks_demote x y hx A t hg.2.1 π hy.2 hp
  have hy' : physicalCell L x (insert t A) π b (promoteTuple x y t) :=
    (promoted_chart_domains_iff L x y hx.antitone hb A a t b hg he π).mpr hy
  have hyk := (physicalCell_iff_box L x y hx.antitone A π hp' b).mp hy k hk
  apply interval_endpoints_of_iff _ _ _ _ (y k) hyk
  intro v
  rw [← physicalCell_update_iff L x y hx.antitone A π hp' b hy k hk v,
    ← physicalCell_update_iff L x (promoteTuple x y t) hx.antitone (insert t A)
      π hp b hy' k (Finset.mem_insert_of_mem hk) v]
  have he' : Function.update y k v a = x t := by
    rw [Function.update_of_ne hka.symm, he]
  have hc : promoteTuple x (Function.update y k v) t =
      Function.update (promoteTuple x y t) k v := by
    simp only [promoteTuple]
    exact Function.update_comm hkt _ _ _
  change _ ↔ physicalCell L x (insert t A) π b _
  rw [← hc]
  exact (promoted_chart_domains_iff L x (Function.update y k v) hx.antitone hb
    A a t b hg he' π).symm

/-- Both marked higher endpoints and the lower mixed endpoint are literal
evaluations of the clipped bounds. Their Boolean labels retain their signs. -/
theorem marked_endpoints_promote {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Icc 0 L)
    (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hg : internalGap A a t b) (he : y a = x t)
    (π : Equiv.Perm (Fin N)) (hp : orderedBlocks (insert t A) π)
    (hy : physicalCell L x A π b y) :
    (if b then physicalHi L x A π b a else physicalLo x A π b a) = x t ∧
    (if b then physicalHi L x (insert t A) π b a else
      physicalLo x (insert t A) π b a) = x t ∧
    (if !b then physicalHi L x (insert t A) π b t else
      physicalLo x (insert t A) π b t) = x t := by
  classical
  have hp' := orderedBlocks_demote x y hx A t hg.2.1 π hy.2 hp
  have hy' : physicalCell L x (insert t A) π b (promoteTuple x y t) :=
    (promoted_chart_domains_iff L x y hx.antitone hb A a t b hg he π).mpr hy
  have hlow := (physicalCell_iff_box L x y hx.antitone A π hp' b).mp hy a hg.1
  have hhigh := (physicalCell_iff_box L x _ hx.antitone (insert t A) π hp b).mp hy'
  have hat : a ≠ t := fun h => hg.2.1 (h ▸ hg.1)
  have hya : promoteTuple x y t a = x t := by simp [promoteTuple, hat, he]
  have hyt : promoteTuple x y t t = x t := by simp [promoteTuple]
  have ha := hhigh a (Finset.mem_insert_of_mem hg.1)
  have ht := hhigh t (Finset.mem_insert_self _ _)
  rw [he] at hlow
  rw [hya] at ha
  rw [hyt] at ht
  have hadj := promoted_chart_adjacent L x y hx A a t b hy.1 hg.1 hg.2.1 he π hy.2 hp
  have hl (D : Finset (Fin N)) (k : Fin N) :=
    (physicalLo_le_iff x D π b k (physicalLo x D π b k)).mp le_rfl
  have hu (D : Finset (Fin N)) (k : Fin N) :=
    (le_physicalHi_iff L x D π b k (physicalHi L x D π b k)).mp le_rfl
  cases b
  · simp only [Bool.false_eq_true, ite_false, Bool.not_false, ite_true] at *
    have ho : π a < π t := by change (π a).val < (π t).val; omega
    exact ⟨le_antisymm hlow.1 ((hl A a).2.2 t hg.2.1 ho),
      le_antisymm ha.1 ((hl (insert t A) a).2.1 t (Finset.mem_insert_self _ _) ⟨by trivial,hg.2.2.1⟩),
      le_antisymm (hu (insert t A) t).1 ht.2⟩
  · simp only [ite_true, Bool.not_true, Bool.false_eq_true, ite_false] at *
    have ho : π t < π a := by change (π t).val < (π a).val; omega
    exact ⟨le_antisymm ((hu A a).2.2 t hg.2.1 ho) hlow.2,
      le_antisymm ((hu (insert t A) a).2.1 t (Finset.mem_insert_self _ _) ⟨by trivial,hg.2.2.1⟩) ha.2,
      le_antisymm ht.1 (hl (insert t A) t).1⟩

theorem physicalInput_bounded {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hb : ∀ k, x k ∈ Icc 0 L) (A : Finset (Fin N)) (b : Bool)
    (hd : physicalDomain L x A y b) : ∀ k, physicalInput x y A k ∈ Icc 0 L := by
  intro k
  by_cases hk : k ∈ A
  · simp only [physicalInput, ite_eq_left hk]
    cases b
    · exact ⟨(hd k hk).1, (hd k hk).2.1.trans (hb k).2⟩
    · exact ⟨(hb k).1.trans (hd k hk).1, (hd k hk).2.1⟩
  · simpa [physicalInput, hk] using hb k

/-- The physical intervals describe the literal BGE1 cell of S,T. -/
theorem physicalCell_iff_actual {m q : ℕ} (L : ℝ) (x y : Fin (m+q) → ℝ)
    (hx : Antitone x) (hb : ∀ k, x k ∈ Icc 0 L)
    (S T : PlacementSubset m q) (b : Bool) :
    physicalCell L x S.1 (inputOrdering S T) b y ↔
      (fun i => y (S.1.orderEmbOfFin S.2 i)) ∈
        closedPhysicalCell L (fun i => x (S.1.orderEmbOfFin S.2 i))
          (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b T := by
  constructor
  · rintro ⟨hd, hs⟩
    refine ⟨(physicalDomain_iff_rectangle L x y hx hb S.1 S.2 b).mp hd, ?_, ?_⟩
    · rw [← physicalInput_inputOrdering S T x y]
      exact hs
    · rw [← physicalInput_inputOrdering S T x y]
      intro k
      exact physicalInput_bounded L x y hb S.1 b hd _
  · intro h
    have hd := (physicalDomain_iff_rectangle L x y hx hb S.1 S.2 b).mpr h.1
    refine ⟨hd, ?_⟩
    rw [physicalInput_inputOrdering]
    exact h.2.1

theorem selectedTuple_update {m q : ℕ} (S : PlacementSubset m q)
    (y : Fin (m+q) → ℝ) (i : Fin m) (v : ℝ) :
    (fun j => Function.update y (S.1.orderEmbOfFin S.2 i) v
      (S.1.orderEmbOfFin S.2 j)) =
      Function.update (fun j => y (S.1.orderEmbOfFin S.2 j)) i v := by
  classical
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp only [Function.update_of_ne h,
      Function.update_of_ne (fun he => h ((S.1.orderEmbOfFin S.2).injective he))]

/-- Exact identification with both actual clipLower/clipUpper evaluations
at every selected physical label of an admitted BGE1 cell. -/
theorem physical_endpoints_eq_actual {m q : ℕ} (L : ℝ) (x y : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S T : PlacementSubset m q) (b : Bool)
    (hy : physicalCell L x S.1 (inputOrdering S T) b y) (i : Fin m) :
    physicalLo x S.1 (inputOrdering S T) b (S.1.orderEmbOfFin S.2 i) =
      clipLower (fun j => x (S.1.orderEmbOfFin S.2 j))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b T i ∧
    physicalHi L x S.1 (inputOrdering S T) b (S.1.orderEmbOfFin S.2 i) =
      clipUpper L (fun j => x (S.1.orderEmbOfFin S.2 j))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b T i := by
  have hb' : ∀ k, x k ∈ Icc 0 L := fun k => ⟨(hb k).1.le,(hb k).2.le⟩
  have hX : (fun j => x (S.1.orderEmbOfFin S.2 j)) ∈ BetheWavefunctions.chamber m L :=
    ⟨fun _ _ h => hx ((S.1.orderEmbOfFin S.2).strictMono h), fun j => hb _⟩
  have hs : Antitone (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) :=
    fun _ _ h => hx.antitone ((S.1ᶜ.orderEmbOfFin (complement_card S)).monotone h)
  have hyk := (physicalCell_iff_box L x y hx.antitone S.1 (inputOrdering S T)
    (inputOrdering_orderedBlocks S T) b).mp hy _ (S.1.orderEmbOfFin_mem S.2 i)
  apply interval_endpoints_of_iff _ _ _ _ _ hyk
  intro v
  rw [← physicalCell_update_iff L x y hx.antitone S.1 (inputOrdering S T)
    (inputOrdering_orderedBlocks S T) b hy _ (S.1.orderEmbOfFin_mem S.2 i) v,
    physicalCell_iff_actual L x _ hx.antitone hb' S T b, selectedTuple_update,
    closedPhysicalCell_eq_box L _ _ b T hX hs (fun j => hb' _)]
  have hybox := (physicalCell_iff_actual L x y hx.antitone hb' S T b).mp hy
  rw [closedPhysicalCell_eq_box L _ _ b T hX hs (fun j => hb' _)] at hybox
  constructor
  · intro h
    exact ⟨by simpa using h.1 i, by simpa using h.2 i⟩
  · intro h
    constructor <;> intro j <;> by_cases hji : j = i
    · subst j; simpa using h.1
    · simpa only [Function.update_of_ne hji] using hybox.1 j
    · subst j; simpa using h.2
    · simpa only [Function.update_of_ne hji] using hybox.2 j

def physicalCorner {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (b : Bool) (ε : Fin N → Bool) : Fin N → ℝ :=
  fun k => if k ∈ A then
    (if ε k then physicalHi L x A π b k else physicalLo x A π b k) else x k

/-- Complete corner-value transport for the oriented lower chart and the
two pinned higher endpoints. Every remaining Boolean label is retained. -/
theorem physicalCorner_promote {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Icc 0 L)
    (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hg : internalGap A a t b) (he : y a = x t)
    (π : Equiv.Perm (Fin N)) (hp : orderedBlocks (insert t A) π)
    (hy : physicalCell L x A π b y) (ε : Fin N → Bool)
    (hea : ε a = b) (het : ε t = !b) :
    physicalCorner L x A π b ε = physicalCorner L x (insert t A) π b ε := by
  classical
  have hm := marked_endpoints_promote L x y hx hb A a t b hg he π hp hy
  funext k
  by_cases hka : k = a
  · subst k
    simp only [physicalCorner, hg.1, Finset.mem_insert_of_mem hg.1, ite_true, hea]
    exact hm.1.trans hm.2.1.symm
  · by_cases hkt : k = t
    · subst k
      simp only [physicalCorner, hg.2.1, ite_false, Finset.mem_insert_self, ite_true, het]
      exact hm.2.2.symm
    · by_cases hk : k ∈ A
      · have hend := physical_endpoints_promote L x y hx hb A a t b hg he π hp hy k hk hka
        simp only [physicalCorner, hk, Finset.mem_insert_of_mem hk, ite_true, hend.1, hend.2]
      · simp [physicalCorner, hk, hkt]

/-- Exchange the colliding original labels, keeping the actual ranks. -/
def exchangedOrdering {N : ℕ} (π : Equiv.Perm (Fin N)) (a t : Fin N) :
    Equiv.Perm (Fin N) := (Equiv.swap a t).trans π

theorem adjacent_swap_lt {N : ℕ} (π : Equiv.Perm (Fin N)) (a t : Fin N)
    (_hat : a ≠ t)
    (hadj : (π a).val = (π t).val+1 ∨ (π t).val = (π a).val+1)
    (k l : Fin N) (hkl : π k < π l)
    (hkat : ¬ (k = a ∧ l = t)) (hkta : ¬ (k = t ∧ l = a)) :
    exchangedOrdering π a t k < exchangedOrdering π a t l := by
  have hn (u v : Fin N) (h : u ≠ v) : (π u).val ≠ (π v).val :=
    fun he => h (π.injective (Fin.ext he))
  by_cases hka : k = a
  · subst k
    have hlt : l ≠ t := fun h => hkat ⟨rfl,h⟩
    have hla : l ≠ a := fun h => (ne_of_lt hkl) (congrArg π h.symm)
    have hh := hn l t hlt
    simp only [exchangedOrdering, Equiv.trans_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hla hlt]
    change (π t).val < (π l).val
    change (π a).val < (π l).val at hkl
    omega
  · by_cases hkt : k = t
    · subst k
      have hla : l ≠ a := fun h => hkta ⟨rfl,h⟩
      have hlt : l ≠ t := fun h => (ne_of_lt hkl) (congrArg π h.symm)
      have hh := hn l a hla
      simp only [exchangedOrdering, Equiv.trans_apply, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hla hlt]
      change (π a).val < (π l).val
      change (π t).val < (π l).val at hkl
      omega
    · by_cases hla : l = a
      · subst l
        have hh := hn k t hkt
        simp only [exchangedOrdering, Equiv.trans_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne hka hkt]
        change (π k).val < (π t).val
        change (π k).val < (π a).val at hkl
        omega
      · by_cases hlt : l = t
        · subst l
          have hh := hn k a hka
          simp only [exchangedOrdering, Equiv.trans_apply, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne hka hkt]
          change (π k).val < (π a).val
          change (π k).val < (π t).val at hkl
          omega
        · simpa only [exchangedOrdering, Equiv.trans_apply,
            Equiv.swap_apply_of_ne_of_ne hka hkt,
            Equiv.swap_apply_of_ne_of_ne hla hlt] using hkl

theorem exchangedOrdering_orderedBlocks {N : ℕ} (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (a t : Fin N) (ha : a ∈ A) (ht : t ∉ A)
    (hp : orderedBlocks A π)
    (hadj : (π a).val = (π t).val+1 ∨ (π t).val = (π a).val+1) :
    orderedBlocks A (exchangedOrdering π a t) := by
  have hat : a ≠ t := fun h => ht (h ▸ ha)
  constructor
  · intro k hk l hl hkl
    exact adjacent_swap_lt π a t hat hadj k l (hp.1 k hk l hl hkl)
      (fun h => ht (h.2 ▸ hl)) (fun h => ht (h.1 ▸ hk))
  · intro k hk l hl hkl
    exact adjacent_swap_lt π a t hat hadj k l (hp.2 k hk l hl hkl)
      (fun h => hk (h.1 ▸ ha)) (fun h => hl (h.2 ▸ ha))

theorem tuple_exchangedOrdering {N : ℕ} (v : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (a t : Fin N) (he : v a = v t) :
    v ∘ (exchangedOrdering π a t).symm = v ∘ π.symm := by
  funext k
  change v (Equiv.swap a t (π.symm k)) = v (π.symm k)
  by_cases hka : π.symm k = a
  · simp [hka, he]
  · by_cases hkt : π.symm k = t
    · simp [hkt, he]
    · simp [Equiv.swap_apply_of_ne_of_ne hka hkt]

/-- The second lower chart is obtained by a literal swap. The tuple and
closed support are preserved on the marked face, even at other collisions. -/
theorem physicalCell_exchanged_iff {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N)) (a t : Fin N)
    (ha : a ∈ A) (ht : t ∉ A) (he : y a = x t) (b : Bool) :
    physicalCell L x A (exchangedOrdering π a t) b y ↔ physicalCell L x A π b y := by
  unfold physicalCell
  rw [tuple_exchangedOrdering (physicalInput x y A) π a t
    (by simp [physicalInput, ha, ht, he])]

/-- Every unmarked clipLower and clipUpper agrees in the two actual lower
charts. The proof compares whole fibers, so no endpoint label is identified
with another when values coincide. -/
theorem physical_endpoints_exchanged {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (a t : Fin N) (ha : a ∈ A) (ht : t ∉ A) (he : y a = x t) (b : Bool)
    (hp : orderedBlocks A π) (hy : physicalCell L x A π b y)
    (k : Fin N) (hk : k ∈ A) (hka : k ≠ a) :
    physicalLo x A π b k = physicalLo x A (exchangedOrdering π a t) b k ∧
      physicalHi L x A π b k = physicalHi L x A (exchangedOrdering π a t) b k := by
  have hadj := mixed_collision_adjacent L x y hx A a t b hy.1 ha ht he π hy.2
  have hp' := exchangedOrdering_orderedBlocks A π a t ha ht hp hadj.symm
  have hy' := (physicalCell_exchanged_iff L x y A π a t ha ht he b).mpr hy
  have hyk := (physicalCell_iff_box L x y hx.antitone A π hp b).mp hy k hk
  apply interval_endpoints_of_iff _ _ _ _ _ hyk
  intro v
  rw [← physicalCell_update_iff L x y hx.antitone A π hp b hy k hk v,
    ← physicalCell_update_iff L x y hx.antitone A (exchangedOrdering π a t) hp' b hy' k hk v]
  exact (physicalCell_exchanged_iff L x (Function.update y k v) A π a t ha ht
    (by rw [Function.update_of_ne hka.symm, he]) b).symm

/-- In a literal BGE1 chart, physicalCorner is precisely the full generated
merged tuple, with the original Boolean assignment pulled back in order. -/
theorem physicalCorner_eq_actual {m q : ℕ} (L : ℝ) (x y : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S T : PlacementSubset m q) (b : Bool)
    (hy : physicalCell L x S.1 (inputOrdering S T) b y) (ε : Fin (m+q) → Bool) :
    physicalCorner L x S.1 (inputOrdering S T) b ε ∘ (inputOrdering S T).symm =
      mergeChart T
        (cornerTuple (clipLower (fun i => x (S.1.orderEmbOfFin S.2 i))
          (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b T)
          (clipUpper L (fun i => x (S.1.orderEmbOfFin S.2 i))
            (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b T)
          (fun i => ε (S.1.orderEmbOfFin S.2 i)))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) := by
  have hp : physicalInput x (physicalCorner L x S.1 (inputOrdering S T) b ε) S.1 =
      physicalCorner L x S.1 (inputOrdering S T) b ε := by
    funext k
    by_cases hk : k ∈ S.1 <;> simp [physicalInput, physicalCorner, hk]
  rw [← hp, physicalInput_inputOrdering]
  congr 1
  funext i
  have he := physical_endpoints_eq_actual L x y hx hb S T b hy i
  simp only [physicalCorner, S.1.orderEmbOfFin_mem S.2 i, ite_true,
    cornerTuple, he.1, he.2]

theorem physicalCorner_mem {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : Antitone x) (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (hp : orderedBlocks A π) (b : Bool) (hy : physicalCell L x A π b y)
    (ε : Fin N → Bool) : physicalCell L x A π b (physicalCorner L x A π b ε) := by
  classical
  rw [physicalCell_iff_box L x _ hx A π hp b]
  have hb := (physicalCell_iff_box L x y hx A π hp b).mp hy
  intro k hk
  have hle := (hb k hk).1.trans (hb k hk).2
  simp only [physicalCorner, hk, ite_true]
  split_ifs <;> exact ⟨by first | exact hle | exact le_rfl,
    by first | exact hle | exact le_rfl⟩

theorem marked_endpoint_exchanged {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (a t : Fin N) (ha : a ∈ A) (ht : t ∉ A) (he : y a = x t) (b : Bool)
    (hp : orderedBlocks (insert t A) π) (hy : physicalCell L x A π b y) :
    (if !b then physicalHi L x A (exchangedOrdering π a t) b a else
      physicalLo x A (exchangedOrdering π a t) b a) = x t := by
  have hp0 := orderedBlocks_demote x y hx A t ht π hy.2 hp
  have hadj := mixed_collision_adjacent L x y hx A a t b hy.1 ha ht he π hy.2
  have hp' := exchangedOrdering_orderedBlocks A π a t ha ht hp0 hadj.symm
  have hy' := (physicalCell_exchanged_iff L x y A π a t ha ht he b).mpr hy
  have h := (physicalCell_iff_box L x y hx.antitone A (exchangedOrdering π a t) hp' b).mp hy' a ha
  rw [he] at h
  have ho := promoted_chart_adjacent L x y hx A a t b hy.1 ha ht he π hy.2 hp
  have hpa : exchangedOrdering π a t a = π t := by simp [exchangedOrdering]
  have hpt : exchangedOrdering π a t t = π a := by simp [exchangedOrdering]
  cases b
  · simp only [Bool.not_false, ite_true]
    have ho' : exchangedOrdering π a t t < exchangedOrdering π a t a := by
      rw [hpa,hpt]
      change (π a).val < (π t).val
      simpa only [Bool.false_eq_true, ite_false] using Nat.lt_of_succ_le (le_of_eq ho.symm)
    have hu := (le_physicalHi_iff L x A (exchangedOrdering π a t) false a _).mp le_rfl
    exact le_antisymm (hu.2.2 t ht ho') h.2
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    have ho' : exchangedOrdering π a t a < exchangedOrdering π a t t := by
      rw [hpa,hpt]
      change (π t).val < (π a).val
      have ho'' : (π a).val = (π t).val+1 := ho
      omega
    have hl := (physicalLo_le_iff x A (exchangedOrdering π a t) true a _).mp le_rfl
    exact le_antisymm h.1 (hl.2.2 t ht ho')

/-- The second lower generated corner uses the opposite endpoint label at
a. All other labels and the complete physical tuple agree termwise. -/
theorem physicalCorner_exchanged {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Icc 0 L)
    (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hg : internalGap A a t b) (he : y a = x t)
    (π : Equiv.Perm (Fin N)) (hp : orderedBlocks (insert t A) π)
    (hy : physicalCell L x A π b y) (ε : Fin N → Bool) (hea : ε a = b) :
    physicalCorner L x A π b ε =
      physicalCorner L x A (exchangedOrdering π a t) b (Function.update ε a (!b)) := by
  classical
  have hp0 := orderedBlocks_demote x y hx A t hg.2.1 π hy.2 hp
  funext k
  by_cases hka : k = a
  · subst k
    simp only [physicalCorner, hg.1, ite_true, hea, Function.update_self]
    exact (marked_endpoints_promote L x y hx hb A a t b hg he π hp hy).1.trans
      (marked_endpoint_exchanged L x y hx A π a t hg.1 hg.2.1 he b hp hy).symm
  · by_cases hk : k ∈ A
    · have hend := physical_endpoints_exchanged L x y hx A π a t hg.1 hg.2.1 he b hp0 hy k hk hka
      simp only [physicalCorner, hk, ite_true, Function.update_of_ne hka, hend.1, hend.2]
    · simp [physicalCorner, hk]

theorem integratedRanks_exchanged {N : ℕ} (A : Finset (Fin N))
    (π : Equiv.Perm (Fin N)) (a t : Fin N) (ha : a ∈ A) (ht : t ∉ A) :
    integratedRanks (exchangedOrdering π a t) A = integratedRanks π (insert t (A.erase a)) := by
  classical
  unfold integratedRanks
  conv_lhs => rw [← Finset.insert_erase ha, Finset.image_insert]
  rw [Finset.image_insert]
  congr 1
  · simp [exchangedOrdering]
  · apply Finset.image_congr
    intro k hk
    have hka := (Finset.mem_erase.mp hk).1
    have hkt : k ≠ t := fun h => ht (h ▸ Finset.mem_of_mem_erase hk)
    simp [exchangedOrdering, Equiv.swap_apply_of_ne_of_ne hka hkt]

theorem physicalOrientation_flip {N : ℕ} (A : Finset (Fin N)) (a : Fin N)
    (ha : a ∈ A) (ε : Fin N → Bool) :
    physicalOrientation A (Function.update ε a (!(ε a))) = -physicalOrientation A ε := by
  classical
  unfold physicalOrientation
  rw [← Finset.mul_prod_erase A _ ha, ← Finset.mul_prod_erase A _ ha]
  simp only [Function.update_self]
  have he : (∏ k ∈ A.erase a, if Function.update ε a (!(ε a)) k then (1 : ℂ) else -1) =
      ∏ k ∈ A.erase a, if ε k then (1 : ℂ) else -1 := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [he]
  cases ε a <;> simp

theorem exchangedOrdering_involutive {N : ℕ} (π : Equiv.Perm (Fin N)) (a t : Fin N) :
    exchangedOrdering (exchangedOrdering π a t) a t = π := by
  ext k
  simp [exchangedOrdering]

/-- The exchanged ordering has exactly one genuine BGE1 subset label. -/
theorem exists_unique_exchangedChart {m q : ℕ} (L : ℝ) (x y : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (S T : PlacementSubset m q) (a t : Fin (m+q))
    (ha : a ∈ S.1) (ht : t ∉ S.1) (he : y a = x t) (b : Bool)
    (hy : physicalCell L x S.1 (inputOrdering S T) b y) :
    ∃! U : PlacementSubset m q,
      inputOrdering S U = exchangedOrdering (inputOrdering S T) a t := by
  have hp := exchangedOrdering_orderedBlocks S.1 (inputOrdering S T) a t ha ht
    (inputOrdering_orderedBlocks S T)
    (mixed_collision_adjacent L x y hx S.1 a t b hy.1 ha ht he _ hy.2).symm
  obtain ⟨U,hU⟩ := (chartOrderingEquiv S).surjective ⟨_,hp⟩
  refine ⟨U, congrArg Subtype.val hU, ?_⟩
  intro V hV
  apply (chartOrderingEquiv S).injective
  apply Subtype.ext
  exact hV.trans (congrArg Subtype.val hU).symm

/-- Empty marked faces correspond exactly. In both directions this uses
the actual closed cells, rather than an oriented integral of an empty box. -/
theorem marked_face_nonempty_iff {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : Antitone x) (hb : ∀ k, x k ∈ Icc 0 L)
    (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hg : internalGap A a t b) (π : Equiv.Perm (Fin N)) :
    (∃ y, y a = x t ∧ physicalCell L x A π b y) ↔
      (∃ y, y a = x t ∧ y t = x t ∧ physicalCell L x (insert t A) π b y) := by
  classical
  have hat : a ≠ t := fun h => hg.2.1 (h ▸ hg.1)
  constructor
  · rintro ⟨y,he,hy⟩
    refine ⟨promoteTuple x y t, by simp [promoteTuple,hat,he], by simp [promoteTuple], ?_⟩
    exact (promoted_chart_domains_iff L x y hx hb A a t b hg he π).mpr hy
  · rintro ⟨y,he,het,hy⟩
    refine ⟨y,he,?_⟩
    apply (promoted_chart_domains_iff L x y hx hb A a t b hg he π).mp
    have hp : promoteTuple x y t = y := by
      simp only [promoteTuple, ← het, Function.update_eq_self]
    simpa only [hp,physicalCell] using hy

def cornerSummand {N : ℕ} (L c : ℝ) (r : Fin N → ℝ) (z : ℂ)
    (x : Fin N → ℝ) (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (b : Bool) (ε : Fin N → Bool) : ℂ :=
  let v := physicalCorner L x A π b ε
  (c : ℂ)^A.card * Complex.exp (Complex.I*z*(physicalOffset L x v A b : ℂ)) *
    physicalOrientation A ε * BetheInternalFaces.primitive c r (v ∘ π.symm) z (integratedRanks π A)

/-- A literal generated lower pair and its pinned higher corner balance
at the positive-c source roots. All endpoint functions, signs, phases,
denominator sets and degree coefficients occur in the displayed summands.
This is for one marked pair; it is not an exhaustive global decomposition. -/
theorem source_generated_corner_balance {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x y : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Icc 0 L)
    (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hg : internalGap A a t b) (he : y a = x t)
    (π : Equiv.Perm (Fin N)) (hp : orderedBlocks (insert t A) π)
    (hy : physicalCell L x A π b y)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (ε : Fin N → Bool) (hea : ε a = b) (het : ε t = !b) :
    cornerSummand L c (BetheSmooth.sourceRoots L n c) z x A π b ε +
      cornerSummand L c (BetheSmooth.sourceRoots L n c) z x A (exchangedOrdering π a t) b
        (Function.update ε a (!b)) +
      cornerSummand L c (BetheSmooth.sourceRoots L n c) z x (insert t A) π b ε = 0 := by
  classical
  let v := physicalCorner L x A π b ε
  have hp0 := orderedBlocks_demote x y hx A t hg.2.1 π hy.2 hp
  have hv := physicalCorner_mem L x y hx.antitone A π hp0 b hy ε
  have hva : v a = x t := by
    change physicalCorner L x A π b ε a = x t
    simp only [physicalCorner, hg.1, ite_true, hea]
    exact (marked_endpoints_promote L x y hx hb A a t b hg he π hp hy).1
  have hvt : v t = x t := by simp [v,physicalCorner,hg.2.1]
  have hinput : physicalInput x v A = v := by
    funext k
    by_cases hk : k ∈ A <;> simp [physicalInput,v,physicalCorner,hk]
  have hswap : physicalCorner L x A (exchangedOrdering π a t) b (Function.update ε a (!b)) = v :=
    (physicalCorner_exchanged L x y hx hb A a t b hg he π hp hy ε hea).symm
  have hhigh : physicalCorner L x (insert t A) π b ε = v :=
    (physicalCorner_promote L x y hx hb A a t b hg he π hp hy ε hea het).symm
  have hphase : physicalOffset L x v (insert t A) b = physicalOffset L x v A b := by
    have hh := physicalOffset_promote L x v A t hg.2.1 b
    have hprom : promoteTuple x v t = v := by simp only [promoteTuple,← hvt,Function.update_eq_self]
    simpa only [hprom] using hh
  have hsign : physicalOrientation A (Function.update ε a (!b)) = -physicalOrientation A ε := by
    rw [← hea]
    exact physicalOrientation_flip A a hg.1 ε
  have hsign0 : physicalOrientation A ε = (if b then 1 else -1) * physicalOrientation (A.erase a) ε := by
    unfold physicalOrientation
    rw [← Finset.mul_prod_erase A _ hg.1, hea]
  have hbal := source_promoted_face_balance_of_chart hL hc hn x v hx A a t hg.1 hg.2.1 b
    hv.1 hva π hv.2 hp z hz ε hea het
  dsimp only at hbal
  rw [hinput] at hbal
  dsimp only [cornerSummand]
  rw [hswap,hhigh,hphase,hsign,
    tuple_exchangedOrdering v π a t (hva.trans hvt.symm),
    integratedRanks_exchanged A π a t hg.1 hg.2.1,
    Finset.card_insert_of_notMem hg.2.1,hsign0]
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hbal ⊢ <;>
    linear_combination hbal

/-- The full phase, including the lower-branch L, agrees with BGE1. -/
theorem physicalOffset_ordered {N m : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (A : Finset (Fin N)) (hA : A.card = m) (b : Bool) :
    physicalOffset L x y A b =
      branchOffset L (fun i => x (A.orderEmbOfFin hA i)) b -
        ∑ i, y (A.orderEmbOfFin hA i) := by
  classical
  have he : (∑ i, (x (A.orderEmbOfFin hA i) - y (A.orderEmbOfFin hA i))) =
      ∑ k ∈ A, (x k - y k) := by
    conv_rhs => rw [← A.image_orderEmbOfFin_univ hA]
    rw [Finset.sum_image (fun _ _ _ _ h => (A.orderEmbOfFin hA).injective h)]
  unfold physicalOffset branchOffset
  rw [← he, Finset.sum_sub_distrib]
  ring

/-- Every pending denominator in a fully generated actual chart. -/
theorem integratedRanks_actual {m q : ℕ} (S T : PlacementSubset m q) :
    integratedRanks (inputOrdering S T) S.1 =
      BethePrimitiveTransport.activeRanks T (firstPositions (p := m) (q := q)) := by
  classical
  unfold integratedRanks BethePrimitiveTransport.activeRanks firstPositions
  conv_lhs => rw [← S.1.image_orderEmbOfFin_univ S.2, Finset.image_image]
  rw [Finset.map_eq_image, Finset.image_image]
  apply Finset.image_congr
  intro i _
  change inputOrdering S T (S.1.orderEmbOfFin S.2 i) =
    mergePermutation T (Fin.castAdd q i)
  rw [inputOrdering_selected, mergePermutation_selected]

/-- A cornerSummand is exactly the corresponding individual BGE1 summand
with c^m from the inherited ordered-subset coefficient. This is termwise;
no sum over several possible marked pairs is asserted. -/
theorem cornerSummand_eq_actual {m q : ℕ} (L c : ℝ) (r : Fin (m+q) → ℝ) (z : ℂ)
    (x y : Fin (m+q) → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S T : PlacementSubset m q) (b : Bool)
    (hy : physicalCell L x S.1 (inputOrdering S T) b y) (ε : Fin (m+q) → Bool) :
    let X := fun i => x (S.1.orderEmbOfFin S.2 i)
    let s := fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)
    let e := fun i => ε (S.1.orderEmbOfFin S.2 i)
    let Y := cornerTuple (clipLower X s b T) (clipUpper L X s b T) e
    cornerSummand L c r z x S.1 (inputOrdering S T) b ε =
      (c : ℂ)^m * orientation e *
        Complex.exp (Complex.I*z*((branchOffset L X b - ∑ i, Y i : ℝ) : ℂ)) *
        BethePrimitiveTransport.chartPrimitive T c r Y s z (firstPositions (p := m) (q := q)) := by
  dsimp only
  have hY : (fun i => physicalCorner L x S.1 (inputOrdering S T) b ε
      (S.1.orderEmbOfFin S.2 i)) =
      cornerTuple (clipLower (fun i => x (S.1.orderEmbOfFin S.2 i))
          (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b T)
        (clipUpper L (fun i => x (S.1.orderEmbOfFin S.2 i))
          (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b T)
        (fun i => ε (S.1.orderEmbOfFin S.2 i)) := by
    funext i
    have he := physical_endpoints_eq_actual L x y hx hb S T b hy i
    simp only [physicalCorner, S.1.orderEmbOfFin_mem S.2 i, ite_true, cornerTuple,he.1,he.2]
  dsimp only [cornerSummand, BethePrimitiveTransport.chartPrimitive]
  rw [physicalOffset_ordered L x _ S.1 S.2 b, hY,
    physicalCorner_eq_actual L x y hx hb S T b hy ε,
    integratedRanks_actual, orientation_ordered, S.2]
  ring

end QuantumNLS.BetheCornerTransport

#print axioms QuantumNLS.BetheCornerTransport.lowerValues
#print axioms QuantumNLS.BetheCornerTransport.upperValues
#print axioms QuantumNLS.BetheCornerTransport.physicalLo
#print axioms QuantumNLS.BetheCornerTransport.physicalHi
#print axioms QuantumNLS.BetheCornerTransport.physicalLo_le_iff
#print axioms QuantumNLS.BetheCornerTransport.le_physicalHi_iff
#print axioms QuantumNLS.BetheCornerTransport.physicalCell
#print axioms QuantumNLS.BetheCornerTransport.selected_antitone
#print axioms QuantumNLS.BetheCornerTransport.physicalCell_iff_box
#print axioms QuantumNLS.BetheCornerTransport.physicalCell_update_iff
#print axioms QuantumNLS.BetheCornerTransport.interval_endpoints_of_iff
#print axioms QuantumNLS.BetheCornerTransport.physical_endpoints_promote
#print axioms QuantumNLS.BetheCornerTransport.marked_endpoints_promote
#print axioms QuantumNLS.BetheCornerTransport.physicalInput_bounded
#print axioms QuantumNLS.BetheCornerTransport.physicalCell_iff_actual
#print axioms QuantumNLS.BetheCornerTransport.selectedTuple_update
#print axioms QuantumNLS.BetheCornerTransport.physical_endpoints_eq_actual
#print axioms QuantumNLS.BetheCornerTransport.physicalCorner
#print axioms QuantumNLS.BetheCornerTransport.physicalCorner_promote
#print axioms QuantumNLS.BetheCornerTransport.exchangedOrdering
#print axioms QuantumNLS.BetheCornerTransport.adjacent_swap_lt
#print axioms QuantumNLS.BetheCornerTransport.exchangedOrdering_orderedBlocks
#print axioms QuantumNLS.BetheCornerTransport.tuple_exchangedOrdering
#print axioms QuantumNLS.BetheCornerTransport.physicalCell_exchanged_iff
#print axioms QuantumNLS.BetheCornerTransport.physical_endpoints_exchanged
#print axioms QuantumNLS.BetheCornerTransport.physicalCorner_eq_actual
#print axioms QuantumNLS.BetheCornerTransport.physicalCorner_mem
#print axioms QuantumNLS.BetheCornerTransport.marked_endpoint_exchanged
#print axioms QuantumNLS.BetheCornerTransport.physicalCorner_exchanged
#print axioms QuantumNLS.BetheCornerTransport.integratedRanks_exchanged
#print axioms QuantumNLS.BetheCornerTransport.physicalOrientation_flip
#print axioms QuantumNLS.BetheCornerTransport.exchangedOrdering_involutive
#print axioms QuantumNLS.BetheCornerTransport.exists_unique_exchangedChart
#print axioms QuantumNLS.BetheCornerTransport.marked_face_nonempty_iff
#print axioms QuantumNLS.BetheCornerTransport.cornerSummand
#print axioms QuantumNLS.BetheCornerTransport.source_generated_corner_balance

#print axioms QuantumNLS.BetheCornerTransport.physicalOffset_ordered

#print axioms QuantumNLS.BetheCornerTransport.integratedRanks_actual

#print axioms QuantumNLS.BetheCornerTransport.cornerSummand_eq_actual

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheCornerTransport.source_generated_corner_balance,
    ``QuantumNLS.BetheCornerTransport.cornerSummand_eq_actual,
    ``QuantumNLS.BetheCornerTransport.physical_endpoints_eq_actual,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_eq_actual,
    ``QuantumNLS.BetheCornerTransport.exists_unique_exchangedChart,
    ``QuantumNLS.BetheCornerTransport.exchangedOrdering_involutive,
    ``QuantumNLS.BetheCornerTransport.marked_face_nonempty_iff,
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
    ``QuantumNLS.BetheCornerTransport.physicalCell_iff_box,
    ``QuantumNLS.BetheCornerTransport.physical_endpoints_promote,
    ``QuantumNLS.BetheCornerTransport.marked_endpoints_promote,
    ``QuantumNLS.BetheCornerTransport.physical_endpoints_exchanged,
    ``QuantumNLS.BetheCornerTransport.marked_endpoint_exchanged,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_promote,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_exchanged,
    ``QuantumNLS.BetheCornerTransport.integratedRanks_exchanged,
    ``QuantumNLS.BetheCornerTransport.physicalOrientation_flip,
    ``QuantumNLS.BetheInputAdjacency.mixed_collision_adjacent,
    ``QuantumNLS.BetheInputAdjacency.chartOrderingEquiv,
    ``QuantumNLS.BetheInputAdjacency.source_promoted_face_balance_of_chart,
    ``QuantumNLS.BetheNeighborPromotion.physicalOffset_promote,
    ``QuantumNLS.BetheGeneratedEndpoints.closedPhysicalCell_eq_box,
    ``QuantumNLS.BetheInternalFaces.source_primitive_internal_face,
    ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
    ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "Corner transport aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Corner transport aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Corner transport aggregate audit PASS: {seen.size} transitive constants across separate roots. Both lower charts, all unmarked clipped endpoints, marked endpoint evaluations, signs, denominator sets and the local generated positive-c triple balance are proved. Actual BGE1 endpoint/corner identification and marked-face empty/nonempty equivalence are proved. The exhaustive multiple-mark signed decomposition, global cyclic/cross-degree sums and spectral assembly remain OPEN."

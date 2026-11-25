import QuantumNLS.BetheSeamProfiles

/-! Reconstruction ingredients for the actual admitted chart/Boolean labels.
All endpoint uniqueness statements exclude the collapsed intervals already
paired in BSP1. No exhaustive triple decomposition is asserted here. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheSeamReconstruction
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport BetheGeneratedLabels BetheSeamProfiles
attribute [local instance] Classical.propDecidable

/-- A noncollapsed interval retains its Boolean endpoint label uniquely. -/
theorem endpoint_boolean_unique (lo hi : ℝ) (h : lo < hi) (e f : Bool)
    (he : (if e then hi else lo) = (if f then hi else lo)) : e = f := by
  cases e <;> cases f <;> simp_all [ne_of_lt h, ne_of_gt h]

/-- The selected Boolean assignment is recovered from the full tuple in
any fixed noncollapsed physical chart. Spectator extension values are ignored. -/
theorem corner_boolean_unique {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N)) (b : Bool)
    (ε δ : Fin N → Bool)
    (hn : ∀ k ∈ A, physicalLo x A π b k < physicalHi L x A π b k)
    (he : physicalCorner L x A π b ε = physicalCorner L x A π b δ) :
    ∀ k ∈ A, ε k = δ k := by
  intro k hk
  apply endpoint_boolean_unique _ _ (hn k hk)
  simpa only [physicalCorner, hk, ite_true] using congrFun he k

/-- At an actual mixed corner the marked Boolean is forced by its rank:
preceding the spectator uses the lower endpoint, following it uses the upper. -/
theorem mixed_corner_orientation {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : Antitone x) (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (hp : orderedBlocks A π) (b : Bool) (ε : Fin N → Bool)
    (hy : physicalCell L x A π b (physicalCorner L x A π b ε))
    (a t : Fin N) (ha : a ∈ A) (ht : t ∉ A)
    (he : physicalCorner L x A π b ε a = x t)
    (hn : physicalLo x A π b a < physicalHi L x A π b a) :
    (ε a = false ↔ π a < π t) ∧ (ε a = true ↔ π t < π a) := by
  have hb := (physicalCell_iff_box L x _ hx A π hp b).mp hy a ha
  rw [he] at hb
  have hat : a ≠ t := fun h => ht (h ▸ ha)
  have hr : π a ≠ π t := fun h => hat (π.injective h)
  have hc : (if ε a then physicalHi L x A π b a else physicalLo x A π b a) = x t := by
    simpa only [physicalCorner, ha, ite_true] using he
  have hlo (h : π a < π t) : physicalLo x A π b a = x t :=
    le_antisymm hb.1 (((physicalLo_le_iff x A π b a _).mp le_rfl).2.2 t ht h)
  have hhi (h : π t < π a) : physicalHi L x A π b a = x t :=
    le_antisymm (((le_physicalHi_iff L x A π b a _).mp le_rfl).2.2 t ht h) hb.2
  rcases lt_or_gt_of_ne hr with h | h
  · have hε : ε a = false := by
      cases heq : ε a
      · rfl
      · have hc' : physicalHi L x A π b a = x t := by simpa [heq] using hc
        exact False.elim ((ne_of_lt hn) ((hlo h).trans hc'.symm))
    simp [hε, h, not_lt_of_gt h]
  · have hε : ε a = true := by
      cases heq : ε a
      · rw [heq] at hc
        simp only [Bool.false_eq_true, ite_false] at hc
        exact False.elim ((ne_of_lt hn) (hc.trans (hhi h).symm))
      · rfl
    simp [hε, h, not_lt_of_gt h]

/-- In each noncollapsed actual lower chart, promotion preserves its rank
permutation exactly when the marked Boolean equals the branch. -/
theorem mixed_corner_incident_iff {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (hp : orderedBlocks A π) (b : Bool) (ε : Fin N → Bool)
    (hy : physicalCell L x A π b (physicalCorner L x A π b ε))
    (a t : Fin N) (ha : a ∈ A) (ht : t ∉ A)
    (he : physicalCorner L x A π b ε a = x t)
    (hn : physicalLo x A π b a < physicalHi L x A π b a) :
    orderedBlocks (insert t A) π ↔ ε a = b := by
  rw [incident_ordering_iff L x _ hx A a t b hy.1 ha ht he π hy.2]
  have ho := mixed_corner_orientation L x hx.antitone A π hp b ε hy a t ha ht he hn
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, hp, true_and]
  · exact ho.1.symm
  · exact ho.2.symm

/-- Every selected-selected seam forces both endpoint Booleans in the
higher chart, provided its two marked intervals are noncollapsed. -/
theorem selected_corner_orientations {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (hp : orderedBlocks A π) (b : Bool) (ε : Fin N → Bool)
    (hy : physicalCell L x A π b (physicalCorner L x A π b ε))
    (i j : Fin N) (hi : i ∈ A) (hj : j ∈ A) (hij : i < j)
    (he : physicalCorner L x A π b ε i = physicalCorner L x A π b ε j)
    (hni : physicalLo x A π b i < physicalHi L x A π b i)
    (hnj : physicalLo x A π b j < physicalHi L x A π b j) :
    ε i = false ∧ ε j = true := by
  have hg := selected_collision_gap L x _ hx A b hy.1 i j hi hj hij he
  have hb := (physicalCell_iff_box L x _ hx.antitone A π hp b).mp hy
  have hbi := hb i hi
  have hbj := hb j hj
  have hci : (if ε i then physicalHi L x A π b i else physicalLo x A π b i) =
      physicalCorner L x A π b ε i := by simp [physicalCorner,hi]
  have hcj : (if ε j then physicalHi L x A π b j else physicalLo x A π b j) =
      physicalCorner L x A π b ε j := by simp [physicalCorner,hj]
  have hlo : physicalLo x A π b i = physicalCorner L x A π b ε i := by
    apply le_antisymm hbi.1
    cases b
    · simp only [Bool.false_eq_true,ite_false] at hg
      rw [hg.2.1]
      exact ((physicalLo_le_iff x A π false i _).mp le_rfl).2.1 j hj ⟨rfl,hij⟩
    · simp only [ite_true] at hg
      rw [hg.2.2]
      exact ((physicalLo_le_iff x A π true i _).mp le_rfl).1
  have hhi : physicalHi L x A π b j = physicalCorner L x A π b ε j := by
    apply le_antisymm _ hbj.2
    cases b
    · simp only [Bool.false_eq_true,ite_false] at hg
      rw [hg.2.2]
      exact ((le_physicalHi_iff L x A π false j _).mp le_rfl).1
    · simp only [ite_true] at hg
      rw [hg.2.1]
      exact ((le_physicalHi_iff L x A π true j _).mp le_rfl).2.1 i hi ⟨rfl,hij⟩
  exact ⟨endpoint_boolean_unique _ _ hni (ε i) false (hci.trans hlo.symm),
    endpoint_boolean_unique _ _ hnj (ε j) true (hcj.trans hhi.symm)⟩

/-- Literal full input for a degree-specific actual branch label. -/
def branchInput {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (S : PlacementSubset m q) (l : BranchLabel m q) : Fin (m+q) → ℝ :=
  mergeChart S
    (cornerTuple
      (clipLower (fun i => x (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l.2.1 l.1)
      (clipUpper L (fun i => x (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l.2.1 l.1) l.2.2)
    (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j))

def branchExtension {m q : ℕ} (S : PlacementSubset m q) (l : BranchLabel m q) :
    Fin (m+q) → Bool :=
  Fin.addCases l.2.2 (fun _ => false) ∘ (mergePermutation S).symm

theorem branchExtension_selected {m q : ℕ} (S : PlacementSubset m q)
    (l : BranchLabel m q) (i : Fin m) :
    branchExtension S l (S.1.orderEmbOfFin S.2 i) = l.2.2 i := by
  rw [← mergePermutation_selected]
  simp only [branchExtension,Function.comp_apply,Equiv.symm_apply_apply,Fin.addCases_left]

theorem branchInput_eq_corner {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (l : BranchLabel m q)
    (hl : branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l) :
    branchInput L x S l = physicalCorner L x S.1 (inputOrdering S l.1) l.2.1
      (branchExtension S l) :=
  (admitted_fullInput_corner L x hx hb S l hl (branchExtension S l)
    (branchExtension_selected S l)).symm

/-- Actual admitted lower-label orientation, in every degree, including
its literal chart and Boolean label rather than a separately chosen corner. -/
theorem admitted_mixed_orientation {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (l : BranchLabel m q)
    (hl : branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l)
    (i : Fin m) (t : Fin (m+q)) (ht : t ∉ S.1)
    (he : branchInput L x S l (S.1.orderEmbOfFin S.2 i) = x t)
    (hn : physicalLo x S.1 (inputOrdering S l.1) l.2.1 (S.1.orderEmbOfFin S.2 i) <
      physicalHi L x S.1 (inputOrdering S l.1) l.2.1 (S.1.orderEmbOfFin S.2 i)) :
    orderedBlocks (insert t S.1) (inputOrdering S l.1) ↔ l.2.2 i = l.2.1 := by
  have hy := admitted_corner_cell L x hx hb S l hl
  change physicalCell L x S.1 (inputOrdering S l.1) l.2.1 (branchInput L x S l) at hy
  rw [branchInput_eq_corner L x hx hb S l hl] at hy he
  simpa only [branchExtension_selected] using
    mixed_corner_incident_iff L x hx S.1 _ (inputOrdering_orderedBlocks S l.1)
      l.2.1 (branchExtension S l) hy _ t (S.1.orderEmbOfFin_mem S.2 i) ht he hn

/-- Reconstruct the unique actual input subset from its physical rank
permutation. This is BIA1's inverse applied as a concrete chart map. -/
def chartOfOrdering {m q : ℕ} (S : PlacementSubset m q)
    (π : Equiv.Perm (Fin (m+q))) (hp : orderedBlocks S.1 π) : PlacementSubset m q :=
  (chartOrderingEquiv S).symm ⟨π,hp⟩

theorem chartOfOrdering_ordering {m q : ℕ} (S : PlacementSubset m q)
    (π : Equiv.Perm (Fin (m+q))) (hp : orderedBlocks S.1 π) :
    inputOrdering S (chartOfOrdering S π hp) = π :=
  congrArg Subtype.val ((chartOrderingEquiv S).apply_symm_apply ⟨π,hp⟩)

theorem chartOfOrdering_inverse {m q : ℕ} (S T : PlacementSubset m q) :
    chartOfOrdering S (inputOrdering S T) (inputOrdering_orderedBlocks S T) = T :=
  (chartOrderingEquiv S).symm_apply_apply T

/-- Reconstruct the literal chart, branch and selected Boolean labels.
The extension on spectators introduces no additional labels. -/
def branchOfOrdering {m q : ℕ} (S : PlacementSubset m q)
    (π : Equiv.Perm (Fin (m+q))) (hp : orderedBlocks S.1 π)
    (b : Bool) (ε : Fin (m+q) → Bool) : BranchLabel m q :=
  (chartOfOrdering S π hp,b,fun i => ε (S.1.orderEmbOfFin S.2 i))

theorem branchOfOrdering_inverse {m q : ℕ} (S : PlacementSubset m q)
    (l : BranchLabel m q) :
    branchOfOrdering S (inputOrdering S l.1) (inputOrdering_orderedBlocks S l.1)
      l.2.1 (branchExtension S l) = l := by
  simp only [branchOfOrdering,chartOfOrdering_inverse,branchExtension_selected]

/-- A genuine nonempty physical cell suffices for admission of the
reconstructed label. No nonempty/cancellation assumption is added to a sum. -/
theorem branchOfOrdering_admitted {m q : ℕ} (L : ℝ) (x y : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (π : Equiv.Perm (Fin (m+q)))
    (hp : orderedBlocks S.1 π) (b : Bool) (ε : Fin (m+q) → Bool)
    (hy : physicalCell L x S.1 π b y) :
    branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j))
      (branchOfOrdering S π hp b ε) := by
  have ho := chartOfOrdering_ordering S π hp
  have hy' : physicalCell L x S.1 (inputOrdering S (chartOfOrdering S π hp)) b y := by
    rw [ho]; exact hy
  intro i
  have h := (physicalCell_iff_box L x y hx.antitone S.1 π hp b).mp hy _
    (S.1.orderEmbOfFin_mem S.2 i)
  have he := physical_endpoints_eq_actual L x y hx hb S (chartOfOrdering S π hp) b hy' i
  rw [ho] at he
  change clipLower _ _ b (chartOfOrdering S π hp) i ≤
    clipUpper L _ _ b (chartOfOrdering S π hp) i
  rw [← he.1,← he.2]
  exact h.1.trans h.2

/-- The reconstructed admitted label evaluates to the complete physical
corner with exactly the requested selected Boolean assignment. -/
theorem branchOfOrdering_input {m q : ℕ} (L : ℝ) (x y : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (π : Equiv.Perm (Fin (m+q)))
    (hp : orderedBlocks S.1 π) (b : Bool) (ε : Fin (m+q) → Bool)
    (hy : physicalCell L x S.1 π b y) :
    branchInput L x S (branchOfOrdering S π hp b ε) =
      physicalCorner L x S.1 π b ε := by
  have hl := branchOfOrdering_admitted L x y hx hb S π hp b ε hy
  have he := admitted_fullInput_corner L x hx hb S (branchOfOrdering S π hp b ε)
    hl ε (fun _ => rfl)
  change physicalCorner L x S.1
    (inputOrdering S (chartOfOrdering S π hp)) b ε = _ at he
  rw [chartOfOrdering_ordering] at he
  exact he.symm

/-- Uniqueness among actual admitted labels from chart, branch and full
input. Noncollapse is used only to recover the individual Boolean labels. -/
theorem admitted_label_unique {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (l u : BranchLabel m q)
    (hl : branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l)
    (hu : branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) u)
    (hc : inputOrdering S l.1 = inputOrdering S u.1) (hbranch : l.2.1 = u.2.1)
    (he : branchInput L x S l = branchInput L x S u)
    (hn : ∀ k ∈ S.1, physicalLo x S.1 (inputOrdering S l.1) l.2.1 k <
      physicalHi L x S.1 (inputOrdering S l.1) l.2.1 k) : l = u := by
  have hchart : l.1 = u.1 := by
    apply (chartOrderingEquiv S).injective
    exact Subtype.ext hc
  have hcorner := he
  rw [branchInput_eq_corner L x hx hb S l hl,
    branchInput_eq_corner L x hx hb S u hu,← hc,← hbranch] at hcorner
  have hbool := corner_boolean_unique L x S.1 _ l.2.1 _ _ hn hcorner
  have hbval : l.2.2 = u.2.2 := by
    funext i
    simpa only [branchExtension_selected] using hbool _ (S.1.orderEmbOfFin_mem S.2 i)
  exact Prod.ext hchart (Prod.ext hbranch hbval)

/-- The actual second lower label: adjacent physical chart exchange and
one Boolean flip. It is defined on literal BGE1 labels. -/
def exchangedBranch {m q : ℕ} (S : PlacementSubset m q) (l : BranchLabel m q)
    (i : Fin m) (t : Fin (m+q))
    (hp : orderedBlocks S.1 (exchangedOrdering (inputOrdering S l.1)
      (S.1.orderEmbOfFin S.2 i) t)) : BranchLabel m q :=
  (chartOfOrdering S _ hp,l.2.1,flipEquiv i l.2.2)

theorem exchangedBranch_ordering {m q : ℕ} (S : PlacementSubset m q)
    (l : BranchLabel m q) (i : Fin m) (t : Fin (m+q))
    (hp : orderedBlocks S.1 (exchangedOrdering (inputOrdering S l.1)
      (S.1.orderEmbOfFin S.2 i) t)) :
    inputOrdering S (exchangedBranch S l i t hp).1 =
      exchangedOrdering (inputOrdering S l.1) (S.1.orderEmbOfFin S.2 i) t :=
  chartOfOrdering_ordering S _ hp

/-- The second-lower reconstruction is an involution on actual labels;
there is no orbit factor or independently counted second copy. -/
theorem exchangedBranch_inverse {m q : ℕ} (S : PlacementSubset m q)
    (l : BranchLabel m q) (i : Fin m) (t : Fin (m+q))
    (hp : orderedBlocks S.1 (exchangedOrdering (inputOrdering S l.1)
      (S.1.orderEmbOfFin S.2 i) t))
    (hq : orderedBlocks S.1 (exchangedOrdering
      (inputOrdering S (exchangedBranch S l i t hp).1) (S.1.orderEmbOfFin S.2 i) t)) :
    exchangedBranch S (exchangedBranch S l i t hp) i t hq = l := by
  apply Prod.ext
  · apply (chartOrderingEquiv S).injective
    apply Subtype.ext
    change inputOrdering S (exchangedBranch S (exchangedBranch S l i t hp) i t hq).1 = inputOrdering S l.1
    rw [exchangedBranch_ordering,exchangedBranch_ordering,exchangedOrdering_involutive]
  · apply Prod.ext
    · rfl
    · change flipEquiv i (flipEquiv i l.2.2) = l.2.2
      exact (flipEquiv i).symm_apply_apply l.2.2

/-- Concrete Boolean extension for the exchanged actual chart. -/
theorem exchangedBranch_eq_reconstruct {m q : ℕ} (S : PlacementSubset m q)
    (l : BranchLabel m q) (i : Fin m) (t : Fin (m+q))
    (hp : orderedBlocks S.1 (exchangedOrdering (inputOrdering S l.1)
      (S.1.orderEmbOfFin S.2 i) t)) :
    exchangedBranch S l i t hp =
      branchOfOrdering S _ hp l.2.1
        (Function.update (branchExtension S l) (S.1.orderEmbOfFin S.2 i) (!(l.2.2 i))) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  funext j
  by_cases hji : j = i
  · subst j
    simp [exchangedBranch,branchOfOrdering,flipEquiv]
  · simp [exchangedBranch,branchOfOrdering,flipEquiv,hji,branchExtension_selected]

/-- Exchange reconstructs an admitted actual second lower with the same
complete input as the oriented first lower. This retains all other endpoint
labels even when other seams occur simultaneously. -/
theorem exchangedBranch_admitted_input {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (l : BranchLabel m q)
    (hl : branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l)
    (i : Fin m) (t : Fin (m+q)) (ht : t ∉ S.1)
    (he : branchInput L x S l (S.1.orderEmbOfFin S.2 i) = x t)
    (hc : orderedBlocks (insert t S.1) (inputOrdering S l.1))
    (hea : l.2.2 i = l.2.1)
    (hp : orderedBlocks S.1 (exchangedOrdering (inputOrdering S l.1)
      (S.1.orderEmbOfFin S.2 i) t)) :
    branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j))
      (exchangedBranch S l i t hp) ∧
      branchInput L x S (exchangedBranch S l i t hp) = branchInput L x S l := by
  have hy := admitted_corner_cell L x hx hb S l hl
  change physicalCell L x S.1 (inputOrdering S l.1) l.2.1 (branchInput L x S l) at hy
  have hy' := (physicalCell_exchanged_iff L x _ S.1 (inputOrdering S l.1)
    (S.1.orderEmbOfFin S.2 i) t (S.1.orderEmbOfFin_mem S.2 i) ht he l.2.1).mpr hy
  have hg := collision_internalGap L x _ hx S.1 (S.1.orderEmbOfFin S.2 i) t
    l.2.1 hy.1 (S.1.orderEmbOfFin_mem S.2 i) ht he
  rw [exchangedBranch_eq_reconstruct S l i t hp]
  constructor
  · exact branchOfOrdering_admitted L x _ hx hb S _ hp _ _ hy'
  · rw [branchOfOrdering_input L x _ hx hb S _ hp _ _ hy',
      branchInput_eq_corner L x hx hb S l hl]
    have h := physicalCorner_exchanged L x (branchInput L x S l) hx
      (fun k => ⟨(hb k).1.le,(hb k).2.le⟩) S.1 (S.1.orderEmbOfFin S.2 i) t
      l.2.1 hg he (inputOrdering S l.1) hc hy (branchExtension S l)
      (by simpa only [branchExtension_selected] using hea)
    simpa only [hea] using h.symm

/-- Literal clipped noncollapse is exactly physical noncollapse on all
selected labels. Thus the hypotheses refer to the original BGE1 intervals. -/
theorem admitted_noncollapsed_iff {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (l : BranchLabel m q)
    (hl : branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l) :
    (∀ k ∈ S.1, physicalLo x S.1 (inputOrdering S l.1) l.2.1 k <
      physicalHi L x S.1 (inputOrdering S l.1) l.2.1 k) ↔
    (∀ i, clipLower (fun j => x (S.1.orderEmbOfFin S.2 j))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l.2.1 l.1 i <
      clipUpper L (fun j => x (S.1.orderEmbOfFin S.2 j))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l.2.1 l.1 i) := by
  have hy := admitted_corner_cell L x hx hb S l hl
  have he := physical_endpoints_eq_actual L x _ hx hb S l.1 l.2.1 hy
  constructor
  · intro hn i
    rw [← (he i).1,← (he i).2]
    exact hn _ (S.1.orderEmbOfFin_mem S.2 i)
  · intro hn k hk
    let i := (S.1.orderIsoOfFin S.2).symm ⟨k,hk⟩
    have hi : S.1.orderEmbOfFin S.2 i = k :=
      congrArg Subtype.val ((S.1.orderIsoOfFin S.2).apply_symm_apply ⟨k,hk⟩)
    rw [← hi,(he i).1,(he i).2]
    exact hn i

/-- The higher marked Booleans are derived from the original admitted
label. Their physical order is false/true on both transfer branches. -/
theorem admitted_selected_orientations {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (l : BranchLabel m q)
    (hl : branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l)
    (i j : Fin m) (hij : i < j)
    (he : branchInput L x S l (S.1.orderEmbOfFin S.2 i) =
      branchInput L x S l (S.1.orderEmbOfFin S.2 j))
    (hn : ∀ k ∈ S.1, physicalLo x S.1 (inputOrdering S l.1) l.2.1 k <
      physicalHi L x S.1 (inputOrdering S l.1) l.2.1 k) :
    l.2.2 i = false ∧ l.2.2 j = true := by
  have hy := admitted_corner_cell L x hx hb S l hl
  change physicalCell L x S.1 (inputOrdering S l.1) l.2.1 (branchInput L x S l) at hy
  rw [branchInput_eq_corner L x hx hb S l hl] at hy he
  simpa only [branchExtension_selected] using
    selected_corner_orientations L x hx S.1 _ (inputOrdering_orderedBlocks S l.1)
      l.2.1 (branchExtension S l) hy _ _ (S.1.orderEmbOfFin_mem S.2 i)
      (S.1.orderEmbOfFin_mem S.2 j) ((S.1.orderEmbOfFin S.2).strictMono hij) he
      (hn _ (S.1.orderEmbOfFin_mem S.2 i)) (hn _ (S.1.orderEmbOfFin_mem S.2 j))

/-- Demotion reconstructs a lower corner and its ordered chart directly
from a higher pinned corner; the complete input and all other seams agree. -/
theorem pinned_corner_demote {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Icc 0 L)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (hp : orderedBlocks A π) (b : Bool) (ε : Fin N → Bool)
    (hy : physicalCell L x A π b (physicalCorner L x A π b ε))
    (a t : Fin N) (hg : promotedGap A a t b)
    (ha : physicalCorner L x A π b ε a = x t)
    (ht : physicalCorner L x A π b ε t = x t)
    (hea : ε a = b) (het : ε t = !b) :
    orderedBlocks (A.erase t) π ∧
    physicalCell L x (A.erase t) π b (physicalCorner L x A π b ε) ∧
    physicalCorner L x (A.erase t) π b ε = physicalCorner L x A π b ε := by
  have hd := selected_seam_demote L x _ A a t b hg hy.1 ha ht
  have hs : Antitone (physicalInput x (physicalCorner L x A π b ε) (A.erase t) ∘ π.symm) := by
    rw [hd.2.2.1]; exact hy.2
  have heA : insert t (A.erase t) = A := Finset.insert_erase hg.2.1
  have hp' : orderedBlocks (insert t (A.erase t)) π := by rw [heA]; exact hp
  have hp0 := orderedBlocks_demote x _ hx (A.erase t) t (by simp) π hs hp'
  have hy0 : physicalCell L x (A.erase t) π b (physicalCorner L x A π b ε) := ⟨hd.2.1,hs⟩
  refine ⟨hp0,hy0,?_⟩
  have h := physicalCorner_promote L x _ hx hb (A.erase t) a t b hd.1 ha π hp' hy0 ε hea het
  rw [heA] at h
  exact h

/-- The degree-specific input is exactly BGL1's original ambient input. -/
theorem fullInput_branchInput {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (d : Fin (N+1))
    (S : PlacementSubset d.val (N-d.val)) (l : BranchLabel d.val (N-d.val)) :
    fullInput L x ⟨d,S,l⟩ = branchInput L (x ∘ ambient d) S l ∘ (ambient d).symm := rfl

/-- Exact original-label profile equality for the two reconstructed lowers.
This is in the same label space used by sum_marks_original, with no degree,
branch or Boolean quotient. It therefore preserves the chosen stratum. -/
theorem actual_exchanged_profiles {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (d : Fin (N+1))
    (S : PlacementSubset d.val (N-d.val)) (l : BranchLabel d.val (N-d.val))
    (hl : admitted L x ⟨d,S,l⟩) (i : Fin d.val) (t : Fin (d.val+(N-d.val)))
    (ht : t ∉ S.1)
    (he : branchInput L (x ∘ ambient d) S l (S.1.orderEmbOfFin S.2 i) = x (ambient d t))
    (hc : orderedBlocks (insert t S.1) (inputOrdering S l.1)) (hea : l.2.2 i = l.2.1)
    (hp : orderedBlocks S.1 (exchangedOrdering (inputOrdering S l.1)
      (S.1.orderEmbOfFin S.2 i) t)) :
    admitted L x ⟨d,S,exchangedBranch S l i t hp⟩ ∧
    fullInput L x ⟨d,S,exchangedBranch S l i t hp⟩ = fullInput L x ⟨d,S,l⟩ ∧
    labelMark L x ⟨d,S,exchangedBranch S l i t hp⟩ = labelMark L x ⟨d,S,l⟩ := by
  have hx' : StrictAnti (x ∘ ambient d) := fun _ _ h => hx h
  have h := exchangedBranch_admitted_input L (x ∘ ambient d) hx' (fun k => hb _)
    S l hl i t ht he hc hea hp
  have hinput : fullInput L x ⟨d,S,exchangedBranch S l i t hp⟩ = fullInput L x ⟨d,S,l⟩ := by
    rw [fullInput_branchInput,fullInput_branchInput,h.2]
  exact ⟨h.1,hinput,congrArg (fun v => chooseSeam (seams v)) hinput⟩

end QuantumNLS.BetheSeamReconstruction


#print axioms QuantumNLS.BetheSeamReconstruction.endpoint_boolean_unique
#print axioms QuantumNLS.BetheSeamReconstruction.corner_boolean_unique
#print axioms QuantumNLS.BetheSeamReconstruction.mixed_corner_orientation
#print axioms QuantumNLS.BetheSeamReconstruction.mixed_corner_incident_iff
#print axioms QuantumNLS.BetheSeamReconstruction.selected_corner_orientations
#print axioms QuantumNLS.BetheSeamReconstruction.branchInput
#print axioms QuantumNLS.BetheSeamReconstruction.branchExtension
#print axioms QuantumNLS.BetheSeamReconstruction.branchExtension_selected
#print axioms QuantumNLS.BetheSeamReconstruction.branchInput_eq_corner
#print axioms QuantumNLS.BetheSeamReconstruction.admitted_mixed_orientation
#print axioms QuantumNLS.BetheSeamReconstruction.chartOfOrdering
#print axioms QuantumNLS.BetheSeamReconstruction.chartOfOrdering_ordering
#print axioms QuantumNLS.BetheSeamReconstruction.chartOfOrdering_inverse
#print axioms QuantumNLS.BetheSeamReconstruction.branchOfOrdering
#print axioms QuantumNLS.BetheSeamReconstruction.branchOfOrdering_inverse
#print axioms QuantumNLS.BetheSeamReconstruction.branchOfOrdering_admitted
#print axioms QuantumNLS.BetheSeamReconstruction.branchOfOrdering_input
#print axioms QuantumNLS.BetheSeamReconstruction.admitted_label_unique
#print axioms QuantumNLS.BetheSeamReconstruction.exchangedBranch
#print axioms QuantumNLS.BetheSeamReconstruction.exchangedBranch_ordering
#print axioms QuantumNLS.BetheSeamReconstruction.exchangedBranch_inverse
#print axioms QuantumNLS.BetheSeamReconstruction.exchangedBranch_eq_reconstruct
#print axioms QuantumNLS.BetheSeamReconstruction.exchangedBranch_admitted_input
#print axioms QuantumNLS.BetheSeamReconstruction.admitted_noncollapsed_iff
#print axioms QuantumNLS.BetheSeamReconstruction.admitted_selected_orientations
#print axioms QuantumNLS.BetheSeamReconstruction.pinned_corner_demote
#print axioms QuantumNLS.BetheSeamReconstruction.fullInput_branchInput
#print axioms QuantumNLS.BetheSeamReconstruction.actual_exchanged_profiles

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheSeamReconstruction.endpoint_boolean_unique,
    ``QuantumNLS.BetheSeamReconstruction.corner_boolean_unique,
    ``QuantumNLS.BetheSeamReconstruction.mixed_corner_orientation,
    ``QuantumNLS.BetheSeamReconstruction.mixed_corner_incident_iff,
    ``QuantumNLS.BetheSeamReconstruction.selected_corner_orientations,
    ``QuantumNLS.BetheSeamReconstruction.branchInput,
    ``QuantumNLS.BetheSeamReconstruction.branchExtension,
    ``QuantumNLS.BetheSeamReconstruction.branchExtension_selected,
    ``QuantumNLS.BetheSeamReconstruction.branchInput_eq_corner,
    ``QuantumNLS.BetheSeamReconstruction.admitted_mixed_orientation,
    ``QuantumNLS.BetheSeamReconstruction.chartOfOrdering,
    ``QuantumNLS.BetheSeamReconstruction.chartOfOrdering_ordering,
    ``QuantumNLS.BetheSeamReconstruction.chartOfOrdering_inverse,
    ``QuantumNLS.BetheSeamReconstruction.branchOfOrdering,
    ``QuantumNLS.BetheSeamReconstruction.branchOfOrdering_inverse,
    ``QuantumNLS.BetheSeamReconstruction.branchOfOrdering_admitted,
    ``QuantumNLS.BetheSeamReconstruction.branchOfOrdering_input,
    ``QuantumNLS.BetheSeamReconstruction.admitted_label_unique,
    ``QuantumNLS.BetheSeamReconstruction.exchangedBranch,
    ``QuantumNLS.BetheSeamReconstruction.exchangedBranch_ordering,
    ``QuantumNLS.BetheSeamReconstruction.exchangedBranch_inverse,
    ``QuantumNLS.BetheSeamReconstruction.exchangedBranch_eq_reconstruct,
    ``QuantumNLS.BetheSeamReconstruction.exchangedBranch_admitted_input,
    ``QuantumNLS.BetheSeamReconstruction.admitted_noncollapsed_iff,
    ``QuantumNLS.BetheSeamReconstruction.admitted_selected_orientations,
    ``QuantumNLS.BetheSeamReconstruction.pinned_corner_demote,
    ``QuantumNLS.BetheSeamReconstruction.fullInput_branchInput,
    ``QuantumNLS.BetheSeamReconstruction.actual_exchanged_profiles,
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
      throwError "Seam reconstruction aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Seam reconstruction aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Seam reconstruction aggregate audit PASS: {seen.size} transitive constants across separate roots. Actual endpoint orientations, chart/Boolean reconstruction with inverse and admission, noncollapsed label uniqueness, second-lower actual label exchange with involution and original-label mark preservation, and pinned higher physical demotion. BSP1 signed partition, collapsed cancellation and fixed local balance audited as separate roots. Exhaustive cross-degree triple partition, exterior survivors, global sums and spectral assembly remain OPEN."

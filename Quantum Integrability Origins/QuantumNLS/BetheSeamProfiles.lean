import QuantumNLS.BetheGeneratedLabels

/-! Full physical coincidence profiles and a triple-invariant choice of seam.
These remember selected/selected seams as well as mixed ones. The choice is
made from the complete profile, never independently from its mixed subset.
The inverse that groups actual Boolean/chart labels into triples is separate. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheSeamProfiles
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport BetheGeneratedLabels
attribute [local instance] Classical.propDecidable

/-- Unordered pairs are stored once, in increasing physical-label order. -/
def seams {N : ℕ} (v : Fin N → ℝ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ v p.1 = v p.2)

theorem mem_seams {N : ℕ} (v : Fin N → ℝ) (i j : Fin N) :
    (i,j) ∈ seams v ↔ i < j ∧ v i = v j := by simp [seams]

/-- One choice from the entire profile. Classical choice is applied to the
profile itself, so equal profiles give equal marks, including at other seams. -/
def chooseSeam {N : ℕ} (P : Finset (Fin N × Fin N)) : Option (Fin N × Fin N) :=
  if h : P.Nonempty then some (Classical.choose h) else none

theorem chooseSeam_eq_none {N : ℕ} (P : Finset (Fin N × Fin N)) :
    chooseSeam P = none ↔ P = ∅ := by
  by_cases h : P.Nonempty
  · simp [chooseSeam, h, h.ne_empty]
  · simp [chooseSeam, Finset.not_nonempty_iff_eq_empty.mp h]

theorem chooseSeam_mem {N : ℕ} (P : Finset (Fin N × Fin N)) (p : Fin N × Fin N)
    (h : chooseSeam P = some p) : p ∈ P := by
  unfold chooseSeam at h
  split_ifs at h with hn
  · have he := Option.some.inj h
    exact he ▸ Classical.choose_spec hn

/-- The complete unsorted input, in the original ambient labels. -/
def fullInput {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N) : Fin N → ℝ :=
  mergeChart l.2.1 (coordinates L x l) (spectatorTuple x l) ∘ (ambient l.1).symm

def labelProfile {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N) :
    Finset (Fin N × Fin N) := seams (fullInput L x l)

def labelMark {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N) :
    Option (Fin N × Fin N) := chooseSeam (labelProfile L x l)

theorem fullInput_selected {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N)
    (i : Fin l.1.val) :
    fullInput L x l (ambient l.1 (l.2.1.1.orderEmbOfFin l.2.1.2 i)) =
      coordinates L x l i := by
  simp only [fullInput, Function.comp_apply, Equiv.symm_apply_apply]
  simpa only [selectedRank, mergePermutation_selected] using
    mergeChart_selected l.2.1 (coordinates L x l) (spectatorTuple x l) i

theorem fullInput_spectator {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N)
    (j : Fin (N-l.1.val)) :
    fullInput L x l (ambient l.1 (l.2.1.1ᶜ.orderEmbOfFin (complement_card l.2.1) j)) =
      spectatorTuple x l j := by
  simp only [fullInput, Function.comp_apply, Equiv.symm_apply_apply]
  simpa only [spectatorRank, mergePermutation_spectator] using
    mergeChart_spectator l.2.1 (coordinates L x l) (spectatorTuple x l) j

/-- Every old mixed candidate occurs in the full profile, with its physical
pair sorted once. The full profile may contain additional selected seams. -/
theorem mixed_mem_labelProfile {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N)
    (a t : Fin N) (h : (a,t) ∈ collisionProfile L x l) :
    (min a t, max a t) ∈ labelProfile L x l := by
  obtain ⟨i,j,he,ha,ht⟩ := (mem_collisionProfile L x l a t).mp h
  have hat : a ≠ t := by
    intro hh
    have hij := (ambient l.1).injective (ha.trans (hh.trans ht.symm))
    have hsel := l.2.1.1.orderEmbOfFin_mem l.2.1.2 i
    have hspec := l.2.1.1ᶜ.orderEmbOfFin_mem (complement_card l.2.1) j
    rw [hij] at hsel
    exact (Finset.mem_compl.mp hspec) hsel
  have heq : fullInput L x l a = fullInput L x l t := by
    rw [← ha, ← ht, fullInput_selected, fullInput_spectator]
    exact he
  unfold labelProfile
  rw [mem_seams]
  rcases lt_or_gt_of_ne hat with hlt | hgt
  · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using And.intro hlt heq
  · simpa [min_eq_right hgt.le, max_eq_left hgt.le] using And.intro hgt heq.symm

/-- Exact inverse and multiplicity-one decomposition by the new mark.
The none stratum means no input coincidences; exterior classification is open. -/
def markEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ) :
    ((p : Option (Fin N × Fin N)) ×
      {l : Label L x // labelMark L x l.1 = p}) ≃ Label L x :=
  Equiv.sigmaFiberEquiv (fun l : Label L x => labelMark L x l.1)

theorem markEquiv_inverse {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : Label L x) :
    (markEquiv L x).symm l = ⟨labelMark L x l.1,l,rfl⟩ := rfl

theorem sum_marks {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ) (x : Fin N → ℝ) :
    (∑ p : Option (Fin N × Fin N),
      ∑ l : {l : Label L x // labelMark L x l.1 = p}, value L c n z x l.1.1) =
      ∑ l : Label L x, value L c n z x l.1 := by
  have h := (markEquiv L x).sum_comp (fun l => value L c n z x l.1)
  rw [Fintype.sum_sigma] at h
  exact h

/-- This partition equals the literal BGE1 all-degree conditional sum,
including every original c^m and both branches, via BGL1 sum_value. -/
theorem sum_marks_original {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (z : ℂ) (x : Fin N → ℝ) :
    (∑ p : Option (Fin N × Fin N),
      ∑ l : {l : Label L x // labelMark L x l.1 = p}, value L c n z x l.1.1) =
      ∑ d : Fin (N+1), (c : ℂ)^d.val *
        ∑ S : PlacementSubset d.val (N-d.val),
          let X := fun i => x (ambient d (S.1.orderEmbOfFin S.2 i))
          let s := fun j => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) j))
          ∑ T : PlacementSubset d.val (N-d.val),
            (sourceCorners L c (n ∘ ambient d) z X s false T +
             sourceCorners L c (n ∘ ambient d) z X s true T) := by
  rw [sum_marks, sum_value]

/-- A selected/selected coincidence is pinned at the actual output seam.
Its branch-oriented pair is adjacent in the selected set. -/
theorem selected_collision_gap {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (b : Bool)
    (hd : physicalDomain L x A y b) (i j : Fin N)
    (hi : i ∈ A) (hj : j ∈ A) (hij : i < j) (he : y i = y j) :
    if b then promotedGap A j i b ∧ y j = x i ∧ y i = x i
    else promotedGap A i j b ∧ y i = x j ∧ y j = x j := by
  cases b
  · simp only [Bool.false_eq_true, ite_false, physicalDomain] at hd ⊢
    have hjx : y j = x j := le_antisymm (hd j hj).2.1 (he ▸ (hd i hi).2.2 j hj hij)
    refine ⟨⟨hi,hj,hij,?_⟩,he.trans hjx,hjx⟩
    intro k hk hkj
    by_contra hki
    have hik : i < k := lt_of_not_ge hki
    have hkx := (hd i hi).2.2 k hk hik
    rw [he,hjx] at hkx
    exact (not_le_of_gt (hx hkj)) hkx
  · simp only [ite_true, physicalDomain] at hd ⊢
    have hix : y i = x i := le_antisymm (he ▸ (hd j hj).2.2 i hi hij) (hd i hi).1
    refine ⟨⟨hj,hi,hij,?_⟩,he.symm.trans hix,hix⟩
    intro k hk hik
    by_contra hjk
    have hkj : k < j := lt_of_not_ge hjk
    have hkx := (hd j hj).2.2 k hk hkj
    rw [← he,hix] at hkx
    exact (not_le_of_gt (hx hik)) hkx

/-- Deleting selected coordinates weakens exactly the all-pairs rectangle
constraints. This lemma does not stipulate a lower chart or its endpoints. -/
theorem domain_subset {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (A B : Finset (Fin N)) (b : Bool) (hAB : A ⊆ B)
    (hd : physicalDomain L x B y b) : physicalDomain L x A y b := by
  intro k hk
  have h := hd k (hAB hk)
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h ⊢
  · exact ⟨h.1,h.2.1,fun j hj hjk => h.2.2 j (hAB hj) hjk⟩
  · exact ⟨h.1,h.2.1,fun j hj hjk => h.2.2 j (hAB hj) hjk⟩

/-- Demoting an output already pinned to its own x coordinate preserves
every physical input value, including every simultaneous other seam. -/
theorem input_erase_pinned {N : ℕ} (x y : Fin N → ℝ)
    (A : Finset (Fin N)) (t : Fin N) (ht : y t = x t) :
    physicalInput x y (A.erase t) = physicalInput x y A := by
  funext k
  by_cases hkt : k = t
  · subst k; simp [physicalInput, ht]
  · simp [physicalInput, Finset.mem_erase, hkt]

/-- Higher selected seams have a genuine lower mixed face with the same
full input. This does not yet reconstruct its Boolean or input-chart labels. -/
theorem selected_seam_demote {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hg : promotedGap A a t b) (hd : physicalDomain L x A y b)
    (ha : y a = x t) (ht : y t = x t) :
    internalGap (A.erase t) a t b ∧ physicalDomain L x (A.erase t) y b ∧
      physicalInput x y (A.erase t) = physicalInput x y A ∧ y a = x t := by
  exact ⟨(internalGap_erase_iff A a t hg.2.1 b).mpr hg,
    domain_subset L x y (A.erase t) A b (Finset.erase_subset t A) hd,
    input_erase_pinned x y A t ht,ha⟩

/-- A selected/selected coincidence is isolated, just like a mixed one.
This rules out three input labels sharing its value without any genericity
assumption on other corners. -/
theorem selected_collision_isolated {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (b : Bool)
    (hd : physicalDomain L x A y b) (i j : Fin N)
    (hi : i ∈ A) (hj : j ∈ A) (hij : i < j) (he : y i = y j) :
    ∀ k, k ≠ i → k ≠ j → physicalInput x y A k ≠ y j := by
  have hg := selected_collision_gap L x y hx A b hd i j hi hj hij he
  cases b
  · simp only [Bool.false_eq_true,ite_false] at hg
    have hdem := selected_seam_demote L x y A i j false hg.1 hd hg.2.1 hg.2.2
    have hiso := collision_isolated L x y hx (A.erase j) i j false hdem.2.1
      hdem.1.1 hdem.1.2.1 hg.2.1
    rw [hdem.2.2.1] at hiso
    simpa only [hg.2.2] using hiso
  · simp only [ite_true] at hg
    have hdem := selected_seam_demote L x y A j i true hg.1 hd hg.2.1 hg.2.2
    have hiso := collision_isolated L x y hx (A.erase i) j i true hdem.2.1
      hdem.1.1 hdem.1.2.1 hg.2.1
    rw [hdem.2.2.1] at hiso
    intro k hki hkj
    simpa only [hg.2.1] using hiso k hkj hki

/-- Two spectator labels cannot be a seam at strictly ordered outputs. -/
theorem seam_has_selected {N : ℕ} (x y : Fin N → ℝ) (hx : StrictAnti x)
    (A : Finset (Fin N)) (i j : Fin N)
    (h : (i,j) ∈ seams (physicalInput x y A)) : i ∈ A ∨ j ∈ A := by
  obtain ⟨hlt,he⟩ := (mem_seams _ i j).mp h
  by_contra hn
  obtain ⟨hni,hnj⟩ := not_or.mp hn
  simp only [physicalInput, hni, hnj, ite_false] at he
  exact (ne_of_lt hlt) (hx.injective he)

/-- Every full-profile pair is a genuine mixed seam or a doubly pinned
selected seam. These cases cover all simultaneous candidates at once. -/
theorem seam_classification {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (b : Bool)
    (hd : physicalDomain L x A y b) (i j : Fin N)
    (h : (i,j) ∈ seams (physicalInput x y A)) :
    (internalGap A i j b ∧ y i = x j) ∨
    (internalGap A j i b ∧ y j = x i) ∨
    (if b then promotedGap A j i b ∧ y j = x i ∧ y i = x i
     else promotedGap A i j b ∧ y i = x j ∧ y j = x j) := by
  have hp := (mem_seams _ i j).mp h
  by_cases hi : i ∈ A
  · by_cases hj : j ∈ A
    · right; right
      have he : y i = y j := by simpa only [physicalInput,hi,hj,ite_true] using hp.2
      exact selected_collision_gap L x y hx A b hd i j hi hj hp.1 he
    · left
      have he : y i = x j := by simpa only [physicalInput,hi,hj,ite_true,ite_false] using hp.2
      exact ⟨collision_internalGap L x y hx A i j b hd hi hj he,he⟩
  · have hj : j ∈ A := (seam_has_selected x y hx A i j h).resolve_left hi
    right; left
    have he : y j = x i := by simpa only [physicalInput,hi,hj,ite_true,ite_false] using hp.2.symm
    exact ⟨collision_internalGap L x y hx A j i b hd hj hi he,he⟩

/-- Every input seam is an isolated pair. Other isolated seams may occur
simultaneously; no exclusion or independent copies of those marks are used. -/
theorem seam_isolated {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (A : Finset (Fin N)) (b : Bool)
    (hd : physicalDomain L x A y b) (i j : Fin N)
    (h : (i,j) ∈ seams (physicalInput x y A)) :
    ∀ k, k ≠ i → k ≠ j → physicalInput x y A k ≠ physicalInput x y A j := by
  have hp := (mem_seams _ i j).mp h
  by_cases hi : i ∈ A
  · by_cases hj : j ∈ A
    · have he : y i = y j := by simpa only [physicalInput,hi,hj,ite_true] using hp.2
      simpa only [physicalInput,hj,ite_true] using
        selected_collision_isolated L x y hx A b hd i j hi hj hp.1 he
    · have he : y i = x j := by simpa only [physicalInput,hi,hj,ite_true,ite_false] using hp.2
      simpa only [physicalInput,hj,ite_false] using
        collision_isolated L x y hx A i j b hd hi hj he
  · have hj : j ∈ A := (seam_has_selected x y hx A i j h).resolve_left hi
    have he : y j = x i := by simpa only [physicalInput,hi,hj,ite_true,ite_false] using hp.2.symm
    have hiso := collision_isolated L x y hx A j i b hd hj hi he
    intro k hki hkj
    simpa only [physicalInput,hj,ite_true,he] using hiso k hkj hki

/-- Full profiles are invariant under all three BCT1 generated corners.
This simultaneously preserves every candidate, not just a chosen seam. -/
theorem triple_profiles {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Icc 0 L)
    (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hg : internalGap A a t b) (he : y a = x t)
    (π : Equiv.Perm (Fin N)) (hp : orderedBlocks (insert t A) π)
    (hy : physicalCell L x A π b y) (ε : Fin N → Bool)
    (hea : ε a = b) (het : ε t = !b) :
    seams (physicalCorner L x A π b ε) =
        seams (physicalCorner L x A (exchangedOrdering π a t) b (Function.update ε a (!b))) ∧
    seams (physicalCorner L x A π b ε) =
        seams (physicalCorner L x (insert t A) π b ε) := by
  exact ⟨congrArg seams (physicalCorner_exchanged L x y hx hb A a t b hg he π hp hy ε hea),
    congrArg seams (physicalCorner_promote L x y hx hb A a t b hg he π hp hy ε hea het)⟩

/-- The profile-based choice agrees in both lowers and the higher, even
when there are simultaneous other collisions or no mixed higher candidate. -/
theorem triple_marks {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Icc 0 L)
    (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hg : internalGap A a t b) (he : y a = x t)
    (π : Equiv.Perm (Fin N)) (hp : orderedBlocks (insert t A) π)
    (hy : physicalCell L x A π b y) (ε : Fin N → Bool)
    (hea : ε a = b) (het : ε t = !b) :
    chooseSeam (seams (physicalCorner L x A π b ε)) =
        chooseSeam (seams (physicalCorner L x A (exchangedOrdering π a t) b (Function.update ε a (!b)))) ∧
    chooseSeam (seams (physicalCorner L x A π b ε)) =
        chooseSeam (seams (physicalCorner L x (insert t A) π b ε)) := by
  have h := triple_profiles L x y hx hb A a t b hg he π hp hy ε hea het
  exact ⟨congrArg chooseSeam h.1,congrArg chooseSeam h.2⟩

/-- The physical profile is attached to the actual admitted BGE1 corner,
not an independently supplied tuple. Any extension of the Boolean assignment
away from the selected set gives the same full physical corner. -/
theorem admitted_fullInput_corner {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (l : BranchLabel m q)
    (hl : branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l)
    (ε : Fin (m+q) → Bool) (hε : ∀ i, ε (S.1.orderEmbOfFin S.2 i) = l.2.2 i) :
    physicalCorner L x S.1 (inputOrdering S l.1) l.2.1 ε =
      mergeChart S
        (cornerTuple (clipLower (fun i => x (S.1.orderEmbOfFin S.2 i))
          (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l.2.1 l.1)
          (clipUpper L (fun i => x (S.1.orderEmbOfFin S.2 i))
          (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l.2.1 l.1) l.2.2)
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) := by
  let Y := cornerTuple (clipLower (fun i => x (S.1.orderEmbOfFin S.2 i))
    (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l.2.1 l.1)
    (clipUpper L (fun i => x (S.1.orderEmbOfFin S.2 i))
    (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) l.2.1 l.1) l.2.2
  have hy := admitted_corner_cell L x hx hb S l hl
  funext k
  obtain ⟨r,rfl⟩ := (mergePermutation S).surjective k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) r
  · rw [mergePermutation_selected]
    have hend := physical_endpoints_eq_actual L x _ hx hb S l.1 l.2.1 hy i
    change physicalCorner L x S.1 (inputOrdering S l.1) l.2.1 ε
      (S.1.orderEmbOfFin S.2 i) = _
    rw [show mergeChart S Y (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j))
        (S.1.orderEmbOfFin S.2 i) = Y i from by simpa only [selectedRank,mergePermutation_selected] using mergeChart_selected S Y _ i]
    simp only [physicalCorner, S.1.orderEmbOfFin_mem S.2 i, ite_true, hε,
      hend.1, hend.2, Y, cornerTuple]
  · rw [mergePermutation_spectator]
    have hn := Finset.mem_compl.mp (S.1ᶜ.orderEmbOfFin_mem (complement_card S) j)
    change physicalCorner L x S.1 (inputOrdering S l.1) l.2.1 ε
      (S.1ᶜ.orderEmbOfFin (complement_card S) j) = _
    rw [show mergeChart S Y (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j))
        (S.1ᶜ.orderEmbOfFin (complement_card S) j) =
        x (S.1ᶜ.orderEmbOfFin (complement_card S) j) from by simpa only [spectatorRank,mergePermutation_spectator] using mergeChart_spectator S Y _ j]
    simp only [physicalCorner, hn, ite_false]

/-- A concrete extension retains each actual selected Boolean label. -/
def assignment {N : ℕ} (l : RawLabel N) : Fin (l.1.val+(N-l.1.val)) → Bool :=
  Fin.addCases l.2.2.2.2 (fun _ => false) ∘ (mergePermutation l.2.1).symm

theorem assignment_selected {N : ℕ} (l : RawLabel N) (i : Fin l.1.val) :
    assignment l (l.2.1.1.orderEmbOfFin l.2.1.2 i) = l.2.2.2.2 i := by
  rw [← mergePermutation_selected]
  simp only [assignment, Function.comp_apply, Equiv.symm_apply_apply, Fin.addCases_left]

/-- The profile used to partition the original sum is exactly the profile
of its actual physical corner, transported back to the original ambient N.
No free corner, endpoint, phase, or normalization is substituted. -/
theorem fullInput_eq_physicalCorner {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (l : Label L x) :
    fullInput L x l.1 =
      physicalCorner L (x ∘ ambient l.1.1) l.1.2.1.1
        (inputOrdering l.1.2.1 l.1.2.2.1) l.1.2.2.2.1 (assignment l.1) ∘
          (ambient l.1.1).symm := by
  have hx' : StrictAnti (x ∘ ambient l.1.1) := by
    intro i j hij
    apply hx
    exact hij
  have h := admitted_fullInput_corner L (x ∘ ambient l.1.1) hx' (fun k => hb _)
    l.1.2.1 l.1.2.2 l.2 (assignment l.1) (assignment_selected l.1)
  exact congrArg (fun v => v ∘ (ambient l.1.1).symm) h.symm

/-- Each chosen profile stratum respects the complete signed BCT1 local
identity, at the actual positive-c roots. This remains a fixed-triple result;
no global enumeration or coverage of triples is used as a premise. -/
theorem source_chosen_corner_balance {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x y : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Icc 0 L)
    (A : Finset (Fin N)) (a t : Fin N) (b : Bool)
    (hg : internalGap A a t b) (he : y a = x t)
    (π : Equiv.Perm (Fin N)) (hp : orderedBlocks (insert t A) π)
    (hy : physicalCell L x A π b y)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (ε : Fin N → Bool) (hea : ε a = b) (het : ε t = !b)
    (p : Option (Fin N × Fin N)) :
    (if chooseSeam (seams (physicalCorner L x A π b ε)) = p then
      cornerSummand L c (BetheSmooth.sourceRoots L n c) z x A π b ε else 0) +
    (if chooseSeam (seams (physicalCorner L x A (exchangedOrdering π a t) b
        (Function.update ε a (!b)))) = p then
      cornerSummand L c (BetheSmooth.sourceRoots L n c) z x A (exchangedOrdering π a t) b
        (Function.update ε a (!b)) else 0) +
    (if chooseSeam (seams (physicalCorner L x (insert t A) π b ε)) = p then
      cornerSummand L c (BetheSmooth.sourceRoots L n c) z x (insert t A) π b ε else 0) = 0 := by
  have hm := triple_marks L x y hx hb A a t b hg he π hp hy ε hea het
  rw [← hm.1, ← hm.2]
  split_ifs
  · exact source_generated_corner_balance hL hc hn x y hx hb A a t b hg he π hp hy z hz ε hea het
  · simp only [add_zero]

/-- A higher doubly pinned selected-selected seam remains in the full
profile. It is never discarded merely because the mixed profile is empty. -/
theorem pinned_seam_mem {N : ℕ} (v x : Fin N → ℝ) (a t : Fin N)
    (hat : a ≠ t) (ha : v a = x t) (ht : v t = x t) :
    (min a t,max a t) ∈ seams v := by
  rw [mem_seams]
  rcases lt_or_gt_of_ne hat with h | h
  · simpa [min_eq_left h.le,max_eq_right h.le] using And.intro h (ha.trans ht.symm)
  · simpa [min_eq_right h.le,max_eq_left h.le] using And.intro h (ht.trans ha.symm)

/-- Collapsed Boolean pairs stay in the same chosen seam stratum. Thus
BGL1's exact sign involution also cancels after the new disjoint partition;
coincident endpoint assignments are retained as distinct labels. -/
theorem sum_collapsed_mark {m q : ℕ} (L c : ℝ) (n : Fin (m+q) → ℤ) (z : ℂ)
    (X : Fin m → ℝ) (s : Fin q → ℝ) (S T : PlacementSubset m q) (b : Bool)
    (i : Fin m) (h : clipLower X s b T i = clipUpper L X s b T i)
    (p : Option (Fin (m+q) × Fin (m+q))) :
    (∑ ε : Fin m → Bool,
      if chooseSeam (seams (mergeChart S
          (cornerTuple (clipLower X s b T) (clipUpper L X s b T) ε) s)) = p
      then branchValue L c n z X s (T,b,ε) else 0) = 0 := by
  let f : (Fin m → Bool) → ℂ := fun ε =>
    if chooseSeam (seams (mergeChart S
        (cornerTuple (clipLower X s b T) (clipUpper L X s b T) ε) s)) = p
    then branchValue L c n z X s (T,b,ε) else 0
  have hf (ε : Fin m → Bool) : f (flipEquiv i ε) = -f ε := by
    dsimp only [f]
    rw [cornerTuple_flip _ _ i h, branchValue_flip L c n z X s T b i h]
    split_ifs <;> ring
  have he := (flipEquiv i).sum_comp f
  simp_rw [hf] at he
  rw [Finset.sum_neg_distrib] at he
  change (∑ ε, f ε) = 0
  linear_combination (-1/2 : ℂ) * he

end QuantumNLS.BetheSeamProfiles


#print axioms QuantumNLS.BetheSeamProfiles.seams
#print axioms QuantumNLS.BetheSeamProfiles.mem_seams
#print axioms QuantumNLS.BetheSeamProfiles.chooseSeam
#print axioms QuantumNLS.BetheSeamProfiles.chooseSeam_eq_none
#print axioms QuantumNLS.BetheSeamProfiles.chooseSeam_mem
#print axioms QuantumNLS.BetheSeamProfiles.fullInput
#print axioms QuantumNLS.BetheSeamProfiles.labelProfile
#print axioms QuantumNLS.BetheSeamProfiles.labelMark
#print axioms QuantumNLS.BetheSeamProfiles.fullInput_selected
#print axioms QuantumNLS.BetheSeamProfiles.fullInput_spectator
#print axioms QuantumNLS.BetheSeamProfiles.mixed_mem_labelProfile
#print axioms QuantumNLS.BetheSeamProfiles.markEquiv
#print axioms QuantumNLS.BetheSeamProfiles.markEquiv_inverse
#print axioms QuantumNLS.BetheSeamProfiles.sum_marks
#print axioms QuantumNLS.BetheSeamProfiles.sum_marks_original
#print axioms QuantumNLS.BetheSeamProfiles.selected_collision_gap
#print axioms QuantumNLS.BetheSeamProfiles.domain_subset
#print axioms QuantumNLS.BetheSeamProfiles.input_erase_pinned
#print axioms QuantumNLS.BetheSeamProfiles.selected_seam_demote
#print axioms QuantumNLS.BetheSeamProfiles.selected_collision_isolated
#print axioms QuantumNLS.BetheSeamProfiles.seam_has_selected
#print axioms QuantumNLS.BetheSeamProfiles.seam_classification
#print axioms QuantumNLS.BetheSeamProfiles.seam_isolated
#print axioms QuantumNLS.BetheSeamProfiles.triple_profiles
#print axioms QuantumNLS.BetheSeamProfiles.triple_marks
#print axioms QuantumNLS.BetheSeamProfiles.admitted_fullInput_corner
#print axioms QuantumNLS.BetheSeamProfiles.assignment
#print axioms QuantumNLS.BetheSeamProfiles.assignment_selected
#print axioms QuantumNLS.BetheSeamProfiles.fullInput_eq_physicalCorner
#print axioms QuantumNLS.BetheSeamProfiles.source_chosen_corner_balance
#print axioms QuantumNLS.BetheSeamProfiles.pinned_seam_mem
#print axioms QuantumNLS.BetheSeamProfiles.sum_collapsed_mark

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheSeamProfiles.seams,
    ``QuantumNLS.BetheSeamProfiles.mem_seams,
    ``QuantumNLS.BetheSeamProfiles.chooseSeam,
    ``QuantumNLS.BetheSeamProfiles.chooseSeam_eq_none,
    ``QuantumNLS.BetheSeamProfiles.chooseSeam_mem,
    ``QuantumNLS.BetheSeamProfiles.fullInput,
    ``QuantumNLS.BetheSeamProfiles.labelProfile,
    ``QuantumNLS.BetheSeamProfiles.labelMark,
    ``QuantumNLS.BetheSeamProfiles.fullInput_selected,
    ``QuantumNLS.BetheSeamProfiles.fullInput_spectator,
    ``QuantumNLS.BetheSeamProfiles.mixed_mem_labelProfile,
    ``QuantumNLS.BetheSeamProfiles.markEquiv,
    ``QuantumNLS.BetheSeamProfiles.markEquiv_inverse,
    ``QuantumNLS.BetheSeamProfiles.sum_marks,
    ``QuantumNLS.BetheSeamProfiles.sum_marks_original,
    ``QuantumNLS.BetheSeamProfiles.selected_collision_gap,
    ``QuantumNLS.BetheSeamProfiles.domain_subset,
    ``QuantumNLS.BetheSeamProfiles.input_erase_pinned,
    ``QuantumNLS.BetheSeamProfiles.selected_seam_demote,
    ``QuantumNLS.BetheSeamProfiles.selected_collision_isolated,
    ``QuantumNLS.BetheSeamProfiles.seam_has_selected,
    ``QuantumNLS.BetheSeamProfiles.seam_classification,
    ``QuantumNLS.BetheSeamProfiles.seam_isolated,
    ``QuantumNLS.BetheSeamProfiles.triple_profiles,
    ``QuantumNLS.BetheSeamProfiles.triple_marks,
    ``QuantumNLS.BetheSeamProfiles.admitted_fullInput_corner,
    ``QuantumNLS.BetheSeamProfiles.assignment,
    ``QuantumNLS.BetheSeamProfiles.assignment_selected,
    ``QuantumNLS.BetheSeamProfiles.fullInput_eq_physicalCorner,
    ``QuantumNLS.BetheSeamProfiles.source_chosen_corner_balance,
    ``QuantumNLS.BetheSeamProfiles.pinned_seam_mem,
    ``QuantumNLS.BetheSeamProfiles.sum_collapsed_mark,
    ``QuantumNLS.BetheGeneratedLabels.source_transferTerm_labels_ae,
    ``QuantumNLS.BetheCornerTransport.source_generated_corner_balance]
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
    ``QuantumNLS.BetheGeneratedLabels.sum_value,
    ``QuantumNLS.BetheGeneratedLabels.source_transferTerm_labels_ae,
    ``QuantumNLS.BetheGeneratedLabels.branchValue_flip,
    ``QuantumNLS.BetheCornerTransport.source_generated_corner_balance,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_promote,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_exchanged,
    ``QuantumNLS.BetheCornerTransport.physical_endpoints_eq_actual,
    ``QuantumNLS.BetheInputAdjacency.collision_isolated,
    ``QuantumNLS.BetheInputAdjacency.collision_internalGap,
    ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
    ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "Seam profile aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Seam profile aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Seam profile aggregate audit PASS: {seen.size} transitive constants across separate roots. Full mixed and selected-selected seam geometry, actual admitted label mark inverse and signed sum, complete profile and mark invariance on every BCT1 local triple, chosen-stratum positive-c local balance and collapsed sign cancellation. Actual cancellation-triple label bijection, exterior classification, global sums and spectral assembly remain OPEN."

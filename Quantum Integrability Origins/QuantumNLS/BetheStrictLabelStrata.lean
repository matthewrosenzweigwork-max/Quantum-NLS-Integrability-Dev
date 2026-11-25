import QuantumNLS.BetheCrossDegreeReconstruction

/-! Strict output data separate all lower and upper endpoint candidates. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheStrictLabelStrata
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport BetheGeneratedLabels BetheSeamProfiles
open BetheSeamReconstruction BetheCrossDegreeReconstruction
attribute [local instance] Classical.propDecidable

/-- No selected physical interval has a common lower and upper candidate
when the original output coordinates are strictly ordered and interior. -/
theorem endpoint_candidates_disjoint {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N)) (b : Bool)
    (k : Fin N) (hk : k ∈ A) :
    Disjoint (lowerValues x A π b k) (upperValues L x A π b k) := by
  rw [Finset.disjoint_left]
  intro v hv hw
  cases b <;>
    simp only [lowerValues,upperValues,Bool.false_eq_true,ite_false,ite_true,
      Finset.mem_insert,Finset.mem_union,Finset.mem_image,Finset.mem_filter,
      Finset.mem_compl,Bool.true_eq_false,and_false,false_and,true_and,exists_false,false_or] at hv hw
  · rcases hv with rfl | ⟨i,⟨hi,hki⟩,rfl⟩ | ⟨i,⟨hi,hpi⟩,rfl⟩
    · rcases hw with he | ⟨j,⟨hj,hpj⟩,he⟩
      · exact (ne_of_gt (hb k).1) he.symm
      · exact (ne_of_gt (hb j).1) he
    · rcases hw with he | ⟨j,⟨hj,hpj⟩,he⟩
      · exact (ne_of_lt (hx hki)) he
      · exact hj ((hx.injective he) ▸ hi)
    · rcases hw with he | ⟨j,⟨hj,hpj⟩,he⟩
      · exact hi ((hx.injective he.symm) ▸ hk)
      · have hij := hx.injective he
        subst j
        exact (not_lt_of_gt hpi) hpj
  · rcases hv with rfl | ⟨i,⟨hi,hpi⟩,rfl⟩
    · rcases hw with he | ⟨j,⟨hj,hjk⟩,he⟩ | ⟨j,⟨hj,hpj⟩,he⟩
      · exact (ne_of_lt (hb k).2) he
      · exact (ne_of_lt (hx hjk)) he.symm
      · exact hj ((hx.injective he) ▸ hk)
    · rcases hw with he | ⟨j,⟨hj,hjk⟩,he⟩ | ⟨j,⟨hj,hpj⟩,he⟩
      · exact (ne_of_lt (hb i).2) he
      · exact hi ((hx.injective he) ▸ hj)
      · have hij := hx.injective he
        subst j
        exact (not_lt_of_gt hpi) hpj

/-- Admission plus separated endpoint candidates implies strict intervals.
No additional generic-corner or noncollapse assumption is required. -/
theorem physicalCell_strict {N : ℕ} (L : ℝ) (x y : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (hp : orderedBlocks A π) (b : Bool) (hy : physicalCell L x A π b y)
    (k : Fin N) (hk : k ∈ A) :
    physicalLo x A π b k < physicalHi L x A π b k := by
  have hle := (physicalCell_iff_box L x y hx.antitone A π hp b).mp hy k hk
  refine lt_of_le_of_ne (hle.1.trans hle.2) ?_
  intro he
  have hd := endpoint_candidates_disjoint L x hx hb A π b k hk
  have hlo : physicalLo x A π b k ∈ lowerValues x A π b k := Finset.max'_mem _ _
  have hhi : physicalHi L x A π b k ∈ upperValues L x A π b k := Finset.min'_mem _ _
  exact (Finset.disjoint_left.mp hd) hlo (he ▸ hhi)

/-- Literal strict BGE1 intervals, in the original finite degree split. -/
def Noncollapsed {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N) : Prop :=
  ∀ i, clipLower (outputTuple x l) (spectatorTuple x l) l.2.2.2.1 l.2.2.1 i <
    clipUpper L (outputTuple x l) (spectatorTuple x l) l.2.2.2.1 l.2.2.1 i

/-- Every admitted original label is physically noncollapsed under the
strict representative hypotheses, in every degree including zero. -/
theorem label_physical_strict {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (k : Fin N) (hk : k ∈ outputSet l) :
    physicalLo x (outputSet l) (ordering l) l.2.2.2.1 k <
      physicalHi L x (outputSet l) (ordering l) l.2.2.2.1 k :=
  physicalCell_strict L x _ hx hb _ _ (outputSet_orderedBlocks l) _
    (label_cell L x hx hb l hl) k hk

/-- This refers to the actual clipLower/clipUpper class used in the sum.
Collapsed pairing is vacuous for strict interior output data. -/
theorem admitted_noncollapsed {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) : Noncollapsed L x l := by
  have hx' : StrictAnti (x ∘ ambient l.1) := fun _ _ h => hx h
  exact (admitted_noncollapsed_iff L (x ∘ ambient l.1) hx' (fun k => hb _)
    l.2.1 l.2.2 hl).mp (fun k hk =>
      physicalCell_strict L (x ∘ ambient l.1) _ hx' (fun k => hb _)
        _ _ (inputOrdering_orderedBlocks l.2.1 l.2.2.1) _
        (admitted_corner_cell L (x ∘ ambient l.1) hx' (fun k => hb _) l.2.1 l.2.2 hl) k hk)

/-- No original collapsed interval can occur in this representative. -/
theorem no_admitted_collapsed {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (i : Fin l.1.val) :
    clipLower (outputTuple x l) (spectatorTuple x l) l.2.2.2.1 l.2.2.1 i ≠
      clipUpper L (outputTuple x l) (spectatorTuple x l) l.2.2.2.1 l.2.2.1 i :=
  ne_of_lt (admitted_noncollapsed L x hx hb l hl i)

/-- Promotion preserves the literal strict class because it preserves
actual admission, rather than because endpoint values forget Booleans. -/
theorem promoteLabel_noncollapsed {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (a t : Fin N)
    (ha : a ∈ outputSet l) (ht : t ∉ outputSet l)
    (he : fullInput L x l a = x t) (hε : booleans l a = l.2.2.2.1)
    (hp : orderedBlocks (insert t (outputSet l)) (ordering l)) :
    Noncollapsed L x (promoteLabel l t hp) :=
  admitted_noncollapsed L x hx hb _
    (promoteLabel_supported L x hx hb l hl a t ha ht he hε hp).1

/-- Every original mixed orientation has a derived incidence decision. -/
theorem mixed_incident_iff {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (a t : Fin N)
    (ha : a ∈ outputSet l) (ht : t ∉ outputSet l)
    (he : fullInput L x l a = x t) :
    orderedBlocks (insert t (outputSet l)) (ordering l) ↔
      booleans l a = l.2.2.2.1 :=
  label_mixed_incident_iff L x hx hb l hl a t ha ht he
    (label_physical_strict L x hx hb l hl a ha)

/-- Higher seam demotion requires no independent noncollapse premises. -/
theorem selected_seam_demote_strict {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (i j : Fin N)
    (hi : i ∈ outputSet l) (hj : j ∈ outputSet l) (hij : i < j)
    (he : fullInput L x l i = fullInput L x l j) :
    if l.2.2.2.1 then
      ∃ hp : orderedBlocks ((outputSet l).erase i) (ordering l),
        admitted L x (demoteLabel l i hp) ∧
        fullInput L x (demoteLabel l i hp) = fullInput L x l ∧
        labelMark L x (demoteLabel l i hp) = labelMark L x l ∧
        Noncollapsed L x (demoteLabel l i hp)
    else
      ∃ hp : orderedBlocks ((outputSet l).erase j) (ordering l),
        admitted L x (demoteLabel l j hp) ∧
        fullInput L x (demoteLabel l j hp) = fullInput L x l ∧
        labelMark L x (demoteLabel l j hp) = labelMark L x l ∧
        Noncollapsed L x (demoteLabel l j hp) := by
  have h := selected_seam_actual_demote L x hx hb l hl i j hi hj hij he
    (label_physical_strict L x hx hb l hl i hi)
    (label_physical_strict L x hx hb l hl j hj)
  cases heq : l.2.2.2.1 <;> simp only [heq,Bool.false_eq_true,ite_false,ite_true] at h ⊢
  · obtain ⟨hp,ha,hv,hm⟩ := h
    exact ⟨hp,ha,hv,hm,admitted_noncollapsed L x hx hb _ ha⟩
  · obtain ⟨hp,ha,hv,hm⟩ := h
    exact ⟨hp,ha,hv,hm,admitted_noncollapsed L x hx hb _ ha⟩

/-- Second-lower reconstruction on the original all-degree labels. The
marked Boolean is flipped, with no extra endpoint-provenance labels. -/
def exchangeLabel {N : ℕ} (l : RawLabel N) (a t : Fin N)
    (hp : orderedBlocks (outputSet l) (exchangedOrdering (ordering l) a t)) : RawLabel N :=
  reconstruct (outputSet l) (exchangedOrdering (ordering l) a t) hp l.2.2.2.1
    (Function.update (booleans l) a (!(booleans l a)))

theorem exchangeLabel_data {N : ℕ} (l : RawLabel N) (a t : Fin N)
    (hp : orderedBlocks (outputSet l) (exchangedOrdering (ordering l) a t)) :
    outputSet (exchangeLabel l a t hp) = outputSet l ∧
    ordering (exchangeLabel l a t hp) = exchangedOrdering (ordering l) a t ∧
    (exchangeLabel l a t hp).2.2.2.1 = l.2.2.2.1 :=
  ⟨reconstruct_outputSet _ _ _ _ _,reconstruct_ordering _ _ _ _ _,rfl⟩

/-- Literal degree and every unmarked Boolean survive the exchange. -/
theorem exchangeLabel_booleans {N : ℕ} (l : RawLabel N) (a t : Fin N)
    (ha : a ∈ outputSet l)
    (hp : orderedBlocks (outputSet l) (exchangedOrdering (ordering l) a t)) :
    booleans (exchangeLabel l a t hp) =
      Function.update (booleans l) a (!(booleans l a)) := by
  funext k
  rw [exchangeLabel,reconstruct_booleans]
  by_cases hk : k ∈ outputSet l
  · simp [hk]
  · have hka : k ≠ a := fun h => hk (h.symm ▸ ha)
    simp [hk,hka,booleans_off l k hk]

theorem exchangeLabel_degree {N : ℕ} (l : RawLabel N) (a t : Fin N)
    (hp : orderedBlocks (outputSet l) (exchangedOrdering (ordering l) a t)) :
    (exchangeLabel l a t hp).1 = l.1 := by
  apply Fin.ext
  rw [← outputSet_card,(exchangeLabel_data l a t hp).1,outputSet_card]

/-- Exact involution on original labels, including their Boolean data. -/
theorem exchangeLabel_inverse {N : ℕ} (l : RawLabel N) (a t : Fin N)
    (ha : a ∈ outputSet l)
    (hp : orderedBlocks (outputSet l) (exchangedOrdering (ordering l) a t))
    (hq : orderedBlocks (outputSet (exchangeLabel l a t hp))
      (exchangedOrdering (ordering (exchangeLabel l a t hp)) a t)) :
    exchangeLabel (exchangeLabel l a t hp) a t hq = l := by
  apply rawLabel_unique
  · rw [(exchangeLabel_data _ _ _ _).1,(exchangeLabel_data _ _ _ _).1]
  · rw [(exchangeLabel_data _ _ _ _).2.1,(exchangeLabel_data _ _ _ _).2.1,
      exchangedOrdering_involutive]
  · rfl
  · have ha' : a ∈ outputSet (exchangeLabel l a t hp) := by
      rw [(exchangeLabel_data _ _ _ _).1]; exact ha
    rw [exchangeLabel_booleans _ _ _ ha' hq,exchangeLabel_booleans _ _ _ ha hp]
    funext k
    by_cases hk : k = a
    · subst k; simp
    · simp [hk]

/-- The two lower summands are distinct original labels. -/
theorem exchangeLabel_ne {N : ℕ} (l : RawLabel N) (a t : Fin N)
    (ha : a ∈ outputSet l)
    (hp : orderedBlocks (outputSet l) (exchangedOrdering (ordering l) a t)) :
    exchangeLabel l a t hp ≠ l := by
  intro he
  have h := congrArg (fun u => booleans u a) he
  rw [exchangeLabel_booleans l a t ha hp,Function.update_self] at h
  cases heq : booleans l a <;> simp [heq] at h

/-- The actual oriented first lower reconstructs the supported second
lower and preserves the full seam profile and literal noncollapsed class. -/
theorem exchangeLabel_supported {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (a t : Fin N)
    (ha : a ∈ outputSet l) (ht : t ∉ outputSet l)
    (he : fullInput L x l a = x t) (hε : booleans l a = l.2.2.2.1)
    (hp : orderedBlocks (outputSet l) (exchangedOrdering (ordering l) a t)) :
    admitted L x (exchangeLabel l a t hp) ∧
    fullInput L x (exchangeLabel l a t hp) = fullInput L x l ∧
    labelMark L x (exchangeLabel l a t hp) = labelMark L x l ∧
    Noncollapsed L x (exchangeLabel l a t hp) := by
  have hy := label_cell L x hx hb l hl
  have hg := collision_internalGap L x _ hx _ a t _ hy.1 ha ht he
  have hinc := (mixed_incident_iff L x hx hb l hl a t ha ht he).mpr hε
  have hy' := (physicalCell_exchanged_iff L x _ _ _ a t ha ht he _).mpr hy
  have hadm := reconstruct_admitted L x _ hx hb _ _ hp _
    (Function.update (booleans l) a (!(booleans l a))) hy'
  have hv := reconstruct_input L x _ hx hb _ _ hp _
    (Function.update (booleans l) a (!(booleans l a))) hy'
  have hc := physicalCorner_exchanged L x _ hx
    (fun k => ⟨(hb k).1.le,(hb k).2.le⟩) _ a t _ hg he _ hinc hy (booleans l) hε
  have hinput : fullInput L x (exchangeLabel l a t hp) = fullInput L x l := by
    have hc' : physicalCorner L x (outputSet l)
        (exchangedOrdering (ordering l) a t) l.2.2.2.1
        (Function.update (booleans l) a (!(booleans l a))) =
        physicalCorner L x (outputSet l) (ordering l) l.2.2.2.1 (booleans l) := by
      simpa only [hε] using hc.symm
    exact hv.trans (hc'.trans (label_corner L x hx hb l hl).symm)
  exact ⟨hadm,hinput,congrArg (fun v => chooseSeam (seams v)) hinput,
    admitted_noncollapsed L x hx hb _ hadm⟩

/-- Both orientations of a mixed corner exchange to the opposite Boolean
in the swapped chart. Unmarked endpoints and the complete input are retained. -/
theorem physicalCorner_exchange_any {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (hp : orderedBlocks A π) (b : Bool) (ε : Fin N → Bool)
    (hy : physicalCell L x A π b (physicalCorner L x A π b ε))
    (a t : Fin N) (ha : a ∈ A) (ht : t ∉ A)
    (he : physicalCorner L x A π b ε a = x t) :
    physicalCorner L x A π b ε =
      physicalCorner L x A (exchangedOrdering π a t) b
        (Function.update ε a (!(ε a))) := by
  have hadj := mixed_collision_adjacent L x _ hx A a t b hy.1 ha ht he π hy.2
  have hp' := exchangedOrdering_orderedBlocks A π a t ha ht hp hadj.symm
  have hy' := (physicalCell_exchanged_iff L x _ A π a t ha ht he b).mpr hy
  have hm := (physicalCell_iff_box L x _ hx.antitone A _ hp' b).mp hy' a ha
  rw [he] at hm
  have ho := mixed_corner_orientation L x hx.antitone A π hp b ε hy a t ha ht he
    (physicalCell_strict L x _ hx hb A π hp b hy a ha)
  funext k
  by_cases hka : k = a
  · subst k
    rw [he]
    cases heq : ε a
    · have hr : exchangedOrdering π a t t < exchangedOrdering π a t a := by
        simpa [exchangedOrdering] using ho.1.mp heq
      have hh : physicalHi L x A (exchangedOrdering π a t) b a = x t :=
        le_antisymm (((le_physicalHi_iff L x A _ b a _).mp le_rfl).2.2 t ht hr) hm.2
      simpa [physicalCorner,ha,heq] using hh.symm
    · have hr : exchangedOrdering π a t a < exchangedOrdering π a t t := by
        simpa [exchangedOrdering] using ho.2.mp heq
      have hh : physicalLo x A (exchangedOrdering π a t) b a = x t :=
        le_antisymm hm.1 (((physicalLo_le_iff x A _ b a _).mp le_rfl).2.2 t ht hr)
      simpa [physicalCorner,ha,heq] using hh.symm
  · by_cases hk : k ∈ A
    · have hend := physical_endpoints_exchanged L x _ hx A π a t ha ht he b hp hy k hk hka
      simp only [physicalCorner,hk,ite_true,Function.update_of_ne hka,hend.1,hend.2]
    · simp [physicalCorner,hk]

/-- Supported second-lower exchange covers both mixed orientations. -/
theorem exchangeLabel_supported_any {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) (a t : Fin N)
    (ha : a ∈ outputSet l) (ht : t ∉ outputSet l)
    (he : fullInput L x l a = x t)
    (hp : orderedBlocks (outputSet l) (exchangedOrdering (ordering l) a t)) :
    admitted L x (exchangeLabel l a t hp) ∧
    fullInput L x (exchangeLabel l a t hp) = fullInput L x l ∧
    labelMark L x (exchangeLabel l a t hp) = labelMark L x l ∧
    Noncollapsed L x (exchangeLabel l a t hp) := by
  have hy := label_cell L x hx hb l hl
  have hy' := (physicalCell_exchanged_iff L x _ _ _ a t ha ht he _).mpr hy
  have hadm := reconstruct_admitted L x _ hx hb _ _ hp _
    (Function.update (booleans l) a (!(booleans l a))) hy'
  have hv := reconstruct_input L x _ hx hb _ _ hp _
    (Function.update (booleans l) a (!(booleans l a))) hy'
  have hc : physicalCorner L x (outputSet l) (ordering l) l.2.2.2.1 (booleans l) =
      physicalCorner L x (outputSet l) (exchangedOrdering (ordering l) a t)
        l.2.2.2.1 (Function.update (booleans l) a (!(booleans l a))) := by
    rw [label_corner L x hx hb l hl] at hy he
    exact physicalCorner_exchange_any L x hx hb _ _ (outputSet_orderedBlocks l) _ _ hy a t ha ht he
  have hinput : fullInput L x (exchangeLabel l a t hp) = fullInput L x l :=
    hv.trans (hc.symm.trans (label_corner L x hx hb l hl).symm)
  exact ⟨hadm,hinput,congrArg (fun v => chooseSeam (seams v)) hinput,
    admitted_noncollapsed L x hx hb _ hadm⟩

/-- Exact original lower labels at a fixed chosen full-profile seam.
Every other simultaneous seam and Boolean remains part of the label. -/
abbrev MixedStratum {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (p : Fin N × Fin N) (a t : Fin N) :=
  {l : RawLabel N // admitted L x l ∧ labelMark L x l = some p ∧
    a ∈ outputSet l ∧ t ∉ outputSet l ∧ fullInput L x l a = x t}

/-- Supported exchange is an equivalence on each entire chosen stratum. -/
def mixedExchange {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (p : Fin N × Fin N) (a t : Fin N) :
    MixedStratum L x p a t ≃ MixedStratum L x p a t where
  toFun l := by
    let hp := label_exchanged_chart L x hx hb l.1 l.2.1 a t l.2.2.2.1
      l.2.2.2.2.1 l.2.2.2.2.2
    have hs := exchangeLabel_supported_any L x hx hb l.1 l.2.1 a t
      l.2.2.2.1 l.2.2.2.2.1 l.2.2.2.2.2 hp
    refine ⟨exchangeLabel l.1 a t hp,hs.1,hs.2.2.1.trans l.2.2.1,?_,?_,?_⟩
    · rw [(exchangeLabel_data _ _ _ _).1]; exact l.2.2.2.1
    · rw [(exchangeLabel_data _ _ _ _).1]; exact l.2.2.2.2.1
    · rw [hs.2.1]; exact l.2.2.2.2.2
  invFun l := by
    let hp := label_exchanged_chart L x hx hb l.1 l.2.1 a t l.2.2.2.1
      l.2.2.2.2.1 l.2.2.2.2.2
    have hs := exchangeLabel_supported_any L x hx hb l.1 l.2.1 a t
      l.2.2.2.1 l.2.2.2.2.1 l.2.2.2.2.2 hp
    refine ⟨exchangeLabel l.1 a t hp,hs.1,hs.2.2.1.trans l.2.2.1,?_,?_,?_⟩
    · rw [(exchangeLabel_data _ _ _ _).1]; exact l.2.2.2.1
    · rw [(exchangeLabel_data _ _ _ _).1]; exact l.2.2.2.2.1
    · rw [hs.2.1]; exact l.2.2.2.2.2
  left_inv l := by
    apply Subtype.ext
    dsimp only
    apply exchangeLabel_inverse
    exact l.2.2.2.1
  right_inv l := by
    apply Subtype.ext
    dsimp only
    apply exchangeLabel_inverse
    exact l.2.2.2.1

theorem mixedExchange_involutive {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (p : Fin N × Fin N) (a t : Fin N) :
    Function.Involutive (mixedExchange L x hx hb p a t) := by
  intro l
  exact (mixedExchange L x hx hb p a t).left_inv l

theorem mixedExchange_ne {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (p : Fin N × Fin N) (a t : Fin N) (l : MixedStratum L x p a t) :
    mixedExchange L x hx hb p a t l ≠ l := by
  intro he
  have he' := congrArg Subtype.val he
  dsimp only [mixedExchange,Equiv.coe_fn_mk] at he'
  exact exchangeLabel_ne l.1 a t l.2.2.2.1
    (label_exchanged_chart L x hx hb l.1 l.2.1 a t l.2.2.2.1
      l.2.2.2.2.1 l.2.2.2.2.2) he' 

/-- Exact degree-by-degree exchange, without a quotient or orbit factor. -/
theorem mixedExchange_degree {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (p : Fin N × Fin N) (a t : Fin N) (l : MixedStratum L x p a t) :
    (mixedExchange L x hx hb p a t l).1.1 = l.1.1 :=
  exchangeLabel_degree l.1 a t
    (label_exchanged_chart L x hx hb l.1 l.2.1 a t l.2.2.2.1
      l.2.2.2.2.1 l.2.2.2.2.2)

/-- Full input, not only the selected seam, is preserved. -/
theorem mixedExchange_input {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (p : Fin N × Fin N) (a t : Fin N) (l : MixedStratum L x p a t) :
    fullInput L x (mixedExchange L x hx hb p a t l).1 = fullInput L x l.1 :=
  (exchangeLabel_supported_any L x hx hb l.1 l.2.1 a t
    l.2.2.2.1 l.2.2.2.2.1 l.2.2.2.2.2
    (label_exchanged_chart L x hx hb l.1 l.2.1 a t l.2.2.2.1
      l.2.2.2.2.1 l.2.2.2.2.2)).2.1

theorem mixedExchange_orientation {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (p : Fin N × Fin N) (a t : Fin N) (l : MixedStratum L x p a t) :
    booleans (mixedExchange L x hx hb p a t l).1 a = !(booleans l.1 a) ∧
    (mixedExchange L x hx hb p a t l).1.2.2.2.1 = l.1.2.2.2.1 := by
  constructor
  · dsimp only [mixedExchange,Equiv.coe_fn_mk]
    rw [exchangeLabel_booleans l.1 a t l.2.2.2.1
      (label_exchanged_chart L x hx hb l.1 l.2.1 a t l.2.2.2.1
        l.2.2.2.2.1 l.2.2.2.2.2),Function.update_self]
  · rfl

/-- First and second lower orientations are equivalent in the actual
chosen-mark stratum, with each original label appearing once. -/
def lowerOrientationEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (p : Fin N × Fin N) (a t : Fin N) :
    {l : MixedStratum L x p a t // booleans l.1 a = l.1.2.2.2.1} ≃
    {l : MixedStratum L x p a t // booleans l.1 a = !(l.1.2.2.2.1)} where
  toFun l := ⟨mixedExchange L x hx hb p a t l.1, by
    rw [(mixedExchange_orientation L x hx hb p a t l.1).1,
      (mixedExchange_orientation L x hx hb p a t l.1).2,l.2]⟩
  invFun l := ⟨mixedExchange L x hx hb p a t l.1, by
    rw [(mixedExchange_orientation L x hx hb p a t l.1).1,
      (mixedExchange_orientation L x hx hb p a t l.1).2,l.2]
    simp⟩
  left_inv l := Subtype.ext (mixedExchange_involutive L x hx hb p a t l.1)
  right_inv l := Subtype.ext (mixedExchange_involutive L x hx hb p a t l.1)

/-- The lower-orientation equivalence has multiplicity one separately
in each literal original degree; it never shifts a summand's degree. -/
theorem lowerOrientationEquiv_degree {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (p : Fin N × Fin N) (a t : Fin N)
    (l : {l : MixedStratum L x p a t // booleans l.1 a = l.1.2.2.2.1}) :
    (lowerOrientationEquiv L x hx hb p a t l).1.1.1 = l.1.1.1 :=
  mixedExchange_degree L x hx hb p a t l.1

end QuantumNLS.BetheStrictLabelStrata


#print axioms QuantumNLS.BetheStrictLabelStrata.endpoint_candidates_disjoint
#print axioms QuantumNLS.BetheStrictLabelStrata.physicalCell_strict
#print axioms QuantumNLS.BetheStrictLabelStrata.Noncollapsed
#print axioms QuantumNLS.BetheStrictLabelStrata.label_physical_strict
#print axioms QuantumNLS.BetheStrictLabelStrata.admitted_noncollapsed
#print axioms QuantumNLS.BetheStrictLabelStrata.no_admitted_collapsed
#print axioms QuantumNLS.BetheStrictLabelStrata.promoteLabel_noncollapsed
#print axioms QuantumNLS.BetheStrictLabelStrata.mixed_incident_iff
#print axioms QuantumNLS.BetheStrictLabelStrata.selected_seam_demote_strict
#print axioms QuantumNLS.BetheStrictLabelStrata.exchangeLabel
#print axioms QuantumNLS.BetheStrictLabelStrata.exchangeLabel_data
#print axioms QuantumNLS.BetheStrictLabelStrata.exchangeLabel_booleans
#print axioms QuantumNLS.BetheStrictLabelStrata.exchangeLabel_degree
#print axioms QuantumNLS.BetheStrictLabelStrata.exchangeLabel_inverse
#print axioms QuantumNLS.BetheStrictLabelStrata.exchangeLabel_ne
#print axioms QuantumNLS.BetheStrictLabelStrata.exchangeLabel_supported
#print axioms QuantumNLS.BetheStrictLabelStrata.physicalCorner_exchange_any
#print axioms QuantumNLS.BetheStrictLabelStrata.exchangeLabel_supported_any
#print axioms QuantumNLS.BetheStrictLabelStrata.MixedStratum
#print axioms QuantumNLS.BetheStrictLabelStrata.mixedExchange
#print axioms QuantumNLS.BetheStrictLabelStrata.mixedExchange_involutive
#print axioms QuantumNLS.BetheStrictLabelStrata.mixedExchange_ne
#print axioms QuantumNLS.BetheStrictLabelStrata.mixedExchange_degree
#print axioms QuantumNLS.BetheStrictLabelStrata.mixedExchange_input
#print axioms QuantumNLS.BetheStrictLabelStrata.mixedExchange_orientation
#print axioms QuantumNLS.BetheStrictLabelStrata.lowerOrientationEquiv
#print axioms QuantumNLS.BetheStrictLabelStrata.lowerOrientationEquiv_degree
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheStrictLabelStrata.endpoint_candidates_disjoint,
    ``QuantumNLS.BetheStrictLabelStrata.physicalCell_strict,
    ``QuantumNLS.BetheStrictLabelStrata.Noncollapsed,
    ``QuantumNLS.BetheStrictLabelStrata.label_physical_strict,
    ``QuantumNLS.BetheStrictLabelStrata.admitted_noncollapsed,
    ``QuantumNLS.BetheStrictLabelStrata.no_admitted_collapsed,
    ``QuantumNLS.BetheStrictLabelStrata.promoteLabel_noncollapsed,
    ``QuantumNLS.BetheStrictLabelStrata.mixed_incident_iff,
    ``QuantumNLS.BetheStrictLabelStrata.selected_seam_demote_strict,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_data,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_booleans,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_degree,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_inverse,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_ne,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_supported,
    ``QuantumNLS.BetheStrictLabelStrata.physicalCorner_exchange_any,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_supported_any,
    ``QuantumNLS.BetheStrictLabelStrata.MixedStratum,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_involutive,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_ne,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_degree,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_input,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_orientation,
    ``QuantumNLS.BetheStrictLabelStrata.lowerOrientationEquiv,
    ``QuantumNLS.BetheStrictLabelStrata.lowerOrientationEquiv_degree,
    ``QuantumNLS.BetheCrossDegreeReconstruction.physicalLabelEquiv,
    ``QuantumNLS.BetheCrossDegreeReconstruction.demote_promote_inverse,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promote_demote_inverse,
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
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Strict label strata nonstandard dependency: {n}"
        | _ => pure ()
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
    ``QuantumNLS.BetheSmooth.sourceRoots,
    ``QuantumNLS.BetheCrossDegreeReconstruction.physicalLabelEquiv,
    ``QuantumNLS.BetheCrossDegreeReconstruction.demote_promote_inverse,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promote_demote_inverse] do
    unless seen.contains n do
      throwError "Strict label strata aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Strict label strata aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Strict label strata aggregate audit PASS: {seen.size} transitive constants across separate roots. Strict original BGE1 noncollapse, supported both-orientation fixed-point-free lower exchange, exact chosen-mark lower equivalence and degree preservation. Inherited physical-label equivalence, supported cross-degree inverses and local signed identities audited separately. Single exhaustive triple equivalence, original signed triple sum, exterior classification, global cancellation and spectral assembly remain OPEN."

import QuantumNLS.BetheMarkedCancellation

/-! Actual adjacent-cut geometry for the reconstructed exterior labels. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheCyclicGeometry
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport BetheGeneratedLabels BetheSeamProfiles
open BetheSeamReconstruction BetheCrossDegreeReconstruction BetheStrictLabelStrata
open BetheExteriorOrigin BetheExteriorCut BetheExteriorSurvivors BetheChartFiberSteps
open BetheExteriorReconstruction BetheExteriorMultiplicity BethePrimitiveTransport
attribute [local instance] Classical.propDecidable

/-- The actual true cut retains L and omits exactly the selected output j. -/
theorem exteriorSelected_true_succ {m : ℕ} (L : ℝ) (X : Fin (m+1) → ℝ)
    (j : Fin (m+1)) :
    exteriorSelected L X true j.succ = Fin.cons (α := fun _ => ℝ) L (X ∘ j.succAbove) := by
  have he : extendedOutput L X true = Fin.cons (α := fun _ => ℝ) L X := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp [extendedOutput]
  rw [exteriorSelected,he,Fin.cons_comp_succ_succAbove]
  rfl

/-- The actual false cut retains 0 and omits the same selected output j. -/
theorem exteriorSelected_false_castSucc {m : ℕ} (L : ℝ) (X : Fin (m+1) → ℝ)
    (j : Fin (m+1)) :
    exteriorSelected L X false j.castSucc = Fin.snoc (α := fun _ => ℝ) (X ∘ j.succAbove) 0 := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · have h : j.castSucc ≤ (Fin.last m).castSucc := by exact_mod_cast j.le_last
    rw [exteriorSelected,Function.comp_apply,Fin.succAbove_of_le_castSucc _ _ h]
    simp [extendedOutput]
  · by_cases h : i.val < j.val
    · have ha : i.castSucc.castSucc < j.castSucc := h
      have hb : i.castSucc < j := h
      rw [exteriorSelected,Function.comp_apply,Fin.succAbove_of_castSucc_lt _ _ ha]
      simp only [extendedOutput,Bool.false_eq_true,ite_false,Fin.val_castSucc,Fin.snoc_castSucc,Function.comp_apply,Fin.succAbove_of_castSucc_lt _ _ hb]
      split_ifs <;> first | rfl | omega
    · have ha : j.castSucc ≤ i.castSucc.castSucc := le_of_not_gt h
      have hb : j ≤ i.castSucc := le_of_not_gt h
      rw [exteriorSelected,Function.comp_apply,Fin.succAbove_of_le_castSucc _ _ ha]
      simp only [extendedOutput,Bool.false_eq_true,ite_false,Fin.val_succ,Fin.val_castSucc,Fin.snoc_castSucc,Function.comp_apply,Fin.succAbove_of_le_castSucc _ _ hb]
      split_ifs <;> first | rfl | omega

/-- The entire displacement on each paired branch is the same omitted X j. -/
theorem paired_branch_displacement {m : ℕ} (L : ℝ) (X : Fin m → ℝ) (j : Fin m) :
    (branchOffset L X true - ∑ i, exteriorSelected L X true j.succ i = X j) ∧
    (branchOffset L X false - ∑ i, exteriorSelected L X false j.castSucc i = X j) := by
  constructor <;> rw [exterior_branch_displacement] <;> simp [extendedOutput,j.isLt]

/-- Adjacent actual cuts differ at precisely one Boolean. -/
theorem cutBooleans_succ_update {m : ℕ} (j : Fin m) :
    cutBooleans j.succ = Function.update (cutBooleans j.castSucc) j true := by
  funext i
  by_cases h : i = j
  · subst i; simp [cutBooleans]
  · rw [Function.update_of_ne h]
    simp only [cutBooleans,Fin.val_succ,Fin.val_castSucc]
    have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
    have he : (i.val < j.val+1) ↔ (i.val < j.val) := by omega
    simp only [he]

/-- The literal product of all endpoint signs reverses in each cyclic pair. -/
theorem paired_orientation {m : ℕ} (j : Fin m) :
    orientation (cutBooleans j.succ) = -orientation (cutBooleans j.castSucc) := by
  cases m with
  | zero => exact Fin.elim0 j
  | succ m =>
    have h (i : Fin m) : cutBooleans j.succ (j.succAbove i) =
        cutBooleans j.castSucc (j.succAbove i) := by
      rw [cutBooleans_succ_update,Function.update_of_ne (Fin.succAbove_ne _ _)]
    unfold orientation
    rw [Fin.prod_univ_succAbove _ j,Fin.prod_univ_succAbove _ j]
    simp only [h]
    simp only [cutBooleans,Fin.val_succ,Fin.val_castSucc,Nat.lt_succ_self,
      decide_true,ite_true,lt_self_iff_false,decide_false,Bool.false_eq_true,ite_false]
    ring

/-- The actual reconstructed merged input is strictly ordered, including its boundary. -/
theorem exteriorChart_strict {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (b : Bool) (r : Fin (m+1)) :
    StrictAnti (mergeChart (exteriorChart L x hx hb S b r)
      (exteriorSelected L (fun i => x (S.1.orderEmbOfFin S.2 i)) b r)
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j))) :=
  (exteriorChart_sorted L x hx hb S b r).strictAnti_of_injective
    ((exterior_append_injective L x hx hb S b r).comp
      (mergePermutation (exteriorChart L x hx hb S b r)).symm.injective)

/-- Bounds pass through the literal chart, without guessing any ranks. -/
theorem mergeChart_bounds {m q : ℕ} (L : ℝ) (T : PlacementSubset m q)
    (Y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : ∀ i, Y i ∈ Icc 0 L) (hs : ∀ j, s j ∈ Icc 0 L) :
    ∀ k, mergeChart T Y s k ∈ Icc 0 L := by
  intro k
  obtain ⟨i,rfl⟩ := (mergePermutation T).surjective k
  cases i using Fin.addCases <;> simp only [mergeChart,Function.comp_apply,
    Equiv.symm_apply_apply,Fin.append_left,Fin.append_right]
  · exact hy _
  · exact hs _

/-- Replacing the maximal boundary by zero and rotating sorts the same tail. -/
theorem antitone_rotate_update_zero {N : ℕ} (hN : 0 < N) (u : Fin N → ℝ)
    (hu : Antitone u) (hb : ∀ i, 0 ≤ u i) :
    Antitone (Function.update u ⟨0,hN⟩ 0 ∘ finRotate N) := by
  cases N with
  | zero => omega
  | succ N =>
    have he : Function.update u (0 : Fin (N+1)) 0 = Fin.cons (α := fun _ => ℝ) (0 : ℝ) (u ∘ Fin.succ) := by
      funext k
      refine Fin.cases ?_ (fun i => ?_) k <;> simp
    have hz : (⟨0,hN⟩ : Fin (N+1)) = 0 := Fin.ext (by simp)
    rw [hz,he]
    change Antitone (fun k => Fin.cons (α := fun _ => ℝ) (0 : ℝ) (u ∘ Fin.succ) (finRotate _ k))
    rw [← Fin.snoc_eq_cons_rotate]
    intro i j hij
    cases i using Fin.lastCases <;> cases j using Fin.lastCases
    · exact le_rfl
    · rename_i j
      have hn : ¬ (Fin.last N ≤ Fin.castSucc j) := not_le_of_gt (Fin.castSucc_lt_last j)
      exact False.elim (hn hij)
    · rename_i i
      simpa only [Fin.snoc_last,Fin.snoc_castSucc,Function.comp_apply] using hb i.succ
    · rename_i i j
      simpa only [Fin.snoc_castSucc,Function.comp_apply] using
        hu (Fin.succ_le_succ_iff.mpr (Fin.castSucc_le_castSucc_iff.mp hij))

/-- The first selected boundary has actual rank zero in the true chart. -/
theorem exterior_true_boundary_rank {m q : ℕ} (L : ℝ) (x : Fin (m+1+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset (m+1) q) (j : Fin (m+1)) :
    selectedRank (exteriorChart L x hx hb S true j.succ) 0 = ⟨0,by omega⟩ := by
  let X := fun i => x (S.1.orderEmbOfFin S.2 i)
  let s := fun k => x (S.1ᶜ.orderEmbOfFin (complement_card S) k)
  let T := exteriorChart L x hx hb S true j.succ
  let Y := exteriorSelected L X true j.succ
  have hY : Y = Fin.cons (α := fun _ => ℝ) L (X ∘ j.succAbove) := exteriorSelected_true_succ L X j
  have hL : 0 < L := (hb (S.1.orderEmbOfFin S.2 j)).1.trans (hb _).2
  have hy : ∀ i, Y i ∈ Icc 0 L := by
    rw [hY]
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [hL.le]
    · simpa using ⟨(hb _).1.le,(hb _).2.le⟩
  have bounds := mergeChart_bounds L T Y s hy (fun k => ⟨(hb _).1.le,(hb _).2.le⟩)
  have hstrict := exteriorChart_strict L x hx hb S true j.succ
  have hy0 : mergeChart T Y s (selectedRank T 0) = L := by
    rw [mergeChart_selected,hY,Fin.cons_zero]
  apply Fin.ext
  change (selectedRank T 0).val = 0
  by_contra h
  have hp : (⟨0,by omega⟩ : Fin (m+1+q)) < selectedRank T 0 := by
    change 0 < (selectedRank T 0).val
    omega
  have hh := hstrict hp
  change mergeChart T Y s (selectedRank T 0) < mergeChart T Y s ⟨0,by omega⟩ at hh
  rw [hy0] at hh
  exact (not_lt_of_ge (bounds _).2) hh

/-- Actual true/false charts are related by rotation of selected labels and
all merged input ranks. No chart correspondence is supplied as a premise. -/
theorem exterior_chart_rotation {m q : ℕ} (L : ℝ) (x : Fin (m+1+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset (m+1) q) (j : Fin (m+1)) :
    mergePermutation (exteriorChart L x hx hb S false j.castSucc) =
      (blockPerm (finRotate (m+1)) (Equiv.refl (Fin q))).trans
        ((mergePermutation (exteriorChart L x hx hb S true j.succ)).trans
          (finRotate (m+1+q)).symm) := by
  let X := fun i => x (S.1.orderEmbOfFin S.2 i)
  let s := fun k => x (S.1ᶜ.orderEmbOfFin (complement_card S) k)
  let W := X ∘ j.succAbove
  let T := exteriorChart L x hx hb S true j.succ
  let U := exteriorChart L x hx hb S false j.castSucc
  let β := blockPerm (finRotate (m+1)) (Equiv.refl (Fin q))
  let ρ := finRotate (m+1+q)
  have hYt := exteriorSelected_true_succ L X j
  have hYf := exteriorSelected_false_castSucc L X j
  have h0 : selectedRank T 0 = ⟨0,by omega⟩ := exterior_true_boundary_rank L x hx hb S j
  have hup : Function.update (Fin.cons (α := fun _ => ℝ) L W) 0 0 = Fin.cons (α := fun _ => ℝ) (0 : ℝ) W := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  have ht : Antitone (mergeChart T (Fin.cons (α := fun _ => ℝ) L W) s) := by
    have h := exteriorChart_sorted L x hx hb S true j.succ
    change Antitone (mergeChart T (exteriorSelected L X true j.succ) s) at h
    rwa [hYt] at h
  have hL : 0 < L := (hb (S.1.orderEmbOfFin S.2 j)).1.trans (hb _).2
  have hpos : ∀ i, 0 ≤ mergeChart T (Fin.cons (α := fun _ => ℝ) L W) s i := by
    apply fun i => (mergeChart_bounds L T (Fin.cons (α := fun _ => ℝ) L W) s ?_ ?_ i).1
    · intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simp [hL.le]
      · simpa using ⟨(hb _).1.le,(hb _).2.le⟩
    · exact fun _ => ⟨(hb _).1.le,(hb _).2.le⟩
  have hr := antitone_rotate_update_zero (show 0 < m+1+q by omega) _ ht hpos
  rw [← h0,← mergeChart_update,hup] at hr
  have happ : Fin.append (Fin.snoc (α := fun _ => ℝ) W 0) s = Fin.append (Fin.cons (α := fun _ => ℝ) (0 : ℝ) W) s ∘ β := by
    funext k
    cases k using Fin.addCases
    · simp only [Function.comp_apply,β,blockPerm_castAdd,Fin.append_left]
      exact congrFun (Fin.snoc_eq_cons_rotate W 0) _
    · simp [β]
  let σ := ρ.trans ((mergePermutation T).symm.trans β.symm)
  have hσ : Antitone (Fin.append (Fin.snoc (α := fun _ => ℝ) W 0) s ∘ σ) := by
    have he : Fin.append (Fin.snoc (α := fun _ => ℝ) W 0) s ∘ σ = mergeChart T (Fin.cons (α := fun _ => ℝ) (0 : ℝ) W) s ∘ ρ := by
      rw [happ]
      funext k
      simp [σ,mergeChart,Function.comp_apply]
    rw [he]
    exact hr
  have hu : Antitone (Fin.append (Fin.snoc (α := fun _ => ℝ) W 0) s ∘ (mergePermutation U).symm) := by
    have h := exteriorChart_sorted L x hx hb S false j.castSucc
    change Antitone (mergeChart U (exteriorSelected L X false j.castSucc) s) at h
    rwa [hYf] at h
  have hinj : Function.Injective (Fin.append (Fin.snoc (α := fun _ => ℝ) W 0) s) := by
    have h := exterior_append_injective L x hx hb S false j.castSucc
    change Function.Injective (Fin.append (exteriorSelected L X false j.castSucc) s) at h
    rwa [hYf] at h
  have he := Tuple.unique_antitone hu hσ
  have heq : (mergePermutation U).symm = σ := Equiv.ext (fun k => hinj (congrFun he k))
  apply Equiv.ext
  intro k
  apply (mergePermutation U).symm.injective
  rw [Equiv.symm_apply_apply,heq]
  change k = σ ((β.trans ((mergePermutation T).trans ρ.symm)) k)
  simp only [σ,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.apply_symm_apply]

/-- Each selected input rank follows the same exact inverse rotation. -/
theorem exterior_selected_rank_rotation {m q : ℕ} (L : ℝ) (x : Fin (m+1+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset (m+1) q) (j i : Fin (m+1)) :
    selectedRank (exteriorChart L x hx hb S false j.castSucc) i =
      (finRotate (m+1+q)).symm
        (selectedRank (exteriorChart L x hx hb S true j.succ) (finRotate (m+1) i)) := by
  simp only [selectedRank,exterior_chart_rotation,Equiv.trans_apply,blockPerm_castAdd]

/-- Every spectator rank follows the same rotation; its label is fixed. -/
theorem exterior_spectator_rank_rotation {m q : ℕ} (L : ℝ) (x : Fin (m+1+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset (m+1) q) (j : Fin (m+1)) (k : Fin q) :
    spectatorRank (exteriorChart L x hx hb S false j.castSucc) k =
      (finRotate (m+1+q)).symm
        (spectatorRank (exteriorChart L x hx hb S true j.succ) k) := by
  simp only [spectatorRank,exterior_chart_rotation,Equiv.trans_apply,blockPerm_natAdd,
    Equiv.refl_apply]

/-- The complete actual pending set rotates; no denominator is omitted. -/
theorem exterior_pending_rotation {m q : ℕ} (L : ℝ) (x : Fin (m+1+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset (m+1) q) (j : Fin (m+1)) :
    activeRanks (exteriorChart L x hx hb S false j.castSucc) firstPositions =
      (activeRanks (exteriorChart L x hx hb S true j.succ) firstPositions).image
        (finRotate (m+1+q)).symm := by
  unfold activeRanks
  rw [exterior_chart_rotation]
  change firstPositions.image ((finRotate (m+1+q)).symm ∘
    mergePermutation (exteriorChart L x hx hb S true j.succ) ∘
      blockPerm (finRotate (m+1)) (Equiv.refl (Fin q))) = _
  rw [← Finset.image_image,← Finset.image_image]
  have he := firstPositions_map_blockPerm (finRotate (m+1)) (Equiv.refl (Fin q))
  simp only [Finset.map_eq_image,Equiv.coe_toEmbedding] at he
  rw [he]

/-- The complete sorted false input is the true sorted input with L replaced
by 0 and moved to the last rank. This is an equality of the actual charts. -/
theorem exterior_merged_rotation {m q : ℕ} (L : ℝ) (x : Fin (m+1+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset (m+1) q) (j : Fin (m+1)) :
    let X := fun i => x (S.1.orderEmbOfFin S.2 i)
    let s := fun k => x (S.1ᶜ.orderEmbOfFin (complement_card S) k)
    mergeChart (exteriorChart L x hx hb S false j.castSucc)
        (exteriorSelected L X false j.castSucc) s =
      Function.update (mergeChart (exteriorChart L x hx hb S true j.succ)
        (exteriorSelected L X true j.succ) s) ⟨0,by omega⟩ 0 ∘ finRotate (m+1+q) := by
  dsimp only
  let X := fun i => x (S.1.orderEmbOfFin S.2 i)
  let s := fun k => x (S.1ᶜ.orderEmbOfFin (complement_card S) k)
  let W := X ∘ j.succAbove
  have hup : Function.update (Fin.cons (α := fun _ => ℝ) L W) 0 0 = Fin.cons (α := fun _ => ℝ) (0 : ℝ) W := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  change mergeChart _ (exteriorSelected L X false j.castSucc) s =
    Function.update (mergeChart _ (exteriorSelected L X true j.succ) s) _ _ ∘ _
  rw [exteriorSelected_true_succ,exteriorSelected_false_castSucc,
    ← exterior_true_boundary_rank L x hx hb S j,← mergeChart_update,hup]
  have happ : Fin.append (Fin.snoc (α := fun _ => ℝ) W 0) s = Fin.append (Fin.cons (α := fun _ => ℝ) (0 : ℝ) W) s ∘
      blockPerm (finRotate (m+1)) (Equiv.refl (Fin q)) := by
    funext k
    cases k using Fin.addCases
    · simp only [Function.comp_apply,blockPerm_castAdd,Fin.append_left]
      exact congrFun (Fin.snoc_eq_cons_rotate W 0) _
    · simp
  unfold mergeChart
  rw [exterior_chart_rotation,happ]
  funext k
  simp only [Function.comp_apply,Equiv.symm_trans_apply,Equiv.apply_symm_apply,
    Equiv.symm_symm]

/-- BCP1 in an arbitrary positive finite dimension, retaining the literal roots. -/
theorem source_primitive_rotate_boundary {N : ℕ} (hN : 0 < N) {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (u : Fin N → ℝ) (hu : u ⟨0,hN⟩ = L) (z : ℂ) (A : Finset (Fin N)) :
    BetheInternalFaces.primitive c (BetheSmooth.sourceRoots L n c) u z A =
      BetheInternalFaces.primitive c (BetheSmooth.sourceRoots L n c)
        (Function.update u ⟨0,hN⟩ 0 ∘ finRotate N) z
        (A.image (finRotate N).symm) := by
  cases N with
  | zero => omega
  | succ N =>
    have he : u = Fin.cons (α := fun _ => ℝ) L (u ∘ Fin.succ) := by
      funext k
      refine Fin.cases ?_ (fun i => ?_) k
      · simp only [Fin.cons_zero]
        have hz : (⟨0,hN⟩ : Fin (N+1)) = 0 := Fin.ext (by simp)
        rw [← hz]
        exact hu
      · simp
    have hz0 : Function.update u (0 : Fin (N+1)) 0 = Fin.cons (α := fun _ => ℝ) (0 : ℝ) (u ∘ Fin.succ) := by
      funext k
      refine Fin.cases ?_ (fun i => ?_) k <;> simp
    have hz : (⟨0,hN⟩ : Fin (N+1)) = 0 := Fin.ext (by simp)
    rw [hz,hz0]
    change _ = BetheInternalFaces.primitive _ _
      (fun k => Fin.cons (α := fun _ => ℝ) (0 : ℝ) (u ∘ Fin.succ) (finRotate _ k)) _ _
    rw [← Fin.snoc_eq_cons_rotate]
    nth_rw 1 [he]
    exact BetheCyclicPrimitives.source_primitive_outer_faces hL hc hn _ z A

/-- Transport the entire primitive on the two actual reconstructed charts,
including all pending denominators. No nonpole hypothesis is required. -/
theorem exterior_chartPrimitive_cyclic {m q : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (m+1+q) → ℤ} (hn : Antitone n)
    (z : ℂ) (x : Fin (m+1+q) → ℝ) (hx : StrictAnti x)
    (hb : ∀ k, x k ∈ Ioo 0 L) (S : PlacementSubset (m+1) q) (j : Fin (m+1)) :
    let X := fun i => x (S.1.orderEmbOfFin S.2 i)
    let s := fun k => x (S.1ᶜ.orderEmbOfFin (complement_card S) k)
    chartPrimitive (exteriorChart L x hx hb S true j.succ) c
        (BetheSmooth.sourceRoots L n c) (exteriorSelected L X true j.succ) s z firstPositions =
      chartPrimitive (exteriorChart L x hx hb S false j.castSucc) c
        (BetheSmooth.sourceRoots L n c) (exteriorSelected L X false j.castSucc) s z firstPositions := by
  dsimp only
  unfold chartPrimitive
  rw [exterior_pending_rotation,exterior_merged_rotation]
  apply source_primitive_rotate_boundary (by omega) hL hc hn
  rw [← exterior_true_boundary_rank L x hx hb S j,mergeChart_selected,
    exteriorSelected_true_succ,Fin.cons_zero]

theorem exterior_chartPrimitive_cyclic_degree {m q : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (m+q) → ℤ} (hn : Antitone n)
    (z : ℂ) (x : Fin (m+q) → ℝ) (hx : StrictAnti x)
    (hb : ∀ k, x k ∈ Ioo 0 L) (S : PlacementSubset m q) (j : Fin m) :
    let X := fun i => x (S.1.orderEmbOfFin S.2 i)
    let s := fun k => x (S.1ᶜ.orderEmbOfFin (complement_card S) k)
    chartPrimitive (exteriorChart L x hx hb S true j.succ) c
        (BetheSmooth.sourceRoots L n c) (exteriorSelected L X true j.succ) s z firstPositions =
      chartPrimitive (exteriorChart L x hx hb S false j.castSucc) c
        (BetheSmooth.sourceRoots L n c) (exteriorSelected L X false j.castSucc) s z firstPositions := by
  cases m with
  | zero => exact Fin.elim0 j
  | succ m => exact exterior_chartPrimitive_cyclic hL hc hn z x hx hb S j

/-- Actual adjacent exterior labels cancel with the full phase and c^m. -/
theorem exteriorValue_cyclic {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) (z : ℂ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (d : Fin (N+1))
    (S : PlacementSubset d.val (N-d.val)) (j : Fin d.val) :
    exteriorValue L c n z x hx hb ⟨d,S,true,j.succ⟩ +
      exteriorValue L c n z x hx hb ⟨d,S,false,j.castSucc⟩ = 0 := by
  have hn' : Antitone (n ∘ ambient d) := fun _ _ h => hn h
  let X := fun i => x (ambient d (S.1.orderEmbOfFin S.2 i))
  have hd := paired_branch_displacement L X j
  have hp : chartPrimitive
      (exteriorChart L (x ∘ ambient d) (fun _ _ h => hx h) (fun _ => hb _) S true j.succ)
      c (BetheSmooth.sourceRoots L (n ∘ ambient d) c)
      (exteriorSelected L X true j.succ)
      (fun k => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) k))) z firstPositions =
    chartPrimitive
      (exteriorChart L (x ∘ ambient d) (fun _ _ h => hx h) (fun _ => hb _) S false j.castSucc)
      c (BetheSmooth.sourceRoots L (n ∘ ambient d) c)
      (exteriorSelected L X false j.castSucc)
      (fun k => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) k))) z firstPositions := by
    exact exterior_chartPrimitive_cyclic_degree hL hc hn' z (x ∘ ambient d)
      (fun _ _ h => hx h) (fun _ => hb _) S j
  unfold exteriorValue
  dsimp only
  change (c : ℂ)^d.val * (orientation (cutBooleans j.succ) *
      Complex.exp (Complex.I*z*((branchOffset L X true - ∑ i, exteriorSelected L X true j.succ i : ℝ) : ℂ)) * _) +
    (c : ℂ)^d.val * (orientation (cutBooleans j.castSucc) *
      Complex.exp (Complex.I*z*((branchOffset L X false - ∑ i, exteriorSelected L X false j.castSucc i : ℝ) : ℂ)) * _) = 0
  rw [hd.1,hd.2,hp,paired_orientation]
  ring

/-- Exact cut telescoping, retaining both endpoint survivors in every degree. -/
theorem sum_exterior_cuts {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) (z : ℂ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (d : Fin (N+1))
    (S : PlacementSubset d.val (N-d.val)) :
    (∑ r : Fin (d.val+1), (exteriorValue L c n z x hx hb ⟨d,S,false,r⟩ +
      exteriorValue L c n z x hx hb ⟨d,S,true,r⟩)) =
      exteriorValue L c n z x hx hb ⟨d,S,true,0⟩ +
        exteriorValue L c n z x hx hb ⟨d,S,false,Fin.last d.val⟩ := by
  rw [Finset.sum_add_distrib,Fin.sum_univ_castSucc,Fin.sum_univ_succ]
  have h : (∑ j : Fin d.val, exteriorValue L c n z x hx hb ⟨d,S,false,j.castSucc⟩) +
      (∑ j : Fin d.val, exteriorValue L c n z x hx hb ⟨d,S,true,j.succ⟩) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    simpa only [add_comm] using exteriorValue_cyclic hL hc hn z x hx hb d S j
  linear_combination h

/-- The actual reconstructed exterior sum reduces globally to its two endpoint
families. In degree zero both original branches are retained unchanged. -/
theorem global_exterior_cyclic_sum {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) (z : ℂ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) :
    (∑ p : ExteriorData N, exteriorValue L c n z x hx hb p) =
      ∑ d : Fin (N+1), ∑ S : PlacementSubset d.val (N-d.val),
        (exteriorValue L c n z x hx hb ⟨d,S,true,0⟩ +
         exteriorValue L c n z x hx hb ⟨d,S,false,Fin.last d.val⟩) := by
  simp only [ExteriorData,Fintype.sum_sigma,Fintype.sum_prod_type,Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro S _
  rw [← Finset.sum_add_distrib]
  simpa only [add_comm] using sum_exterior_cuts hL hc hn z x hx hb d S

/-- The interior arms are subsets of the actual reconstructed admitted,
none-mark original labels, with the exact original d and S fixed. -/
abbrev CyclicArm {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (hx : StrictAnti x)
    (hb : ∀ k, x k ∈ Ioo 0 L) (d : Fin (N+1))
    (S : PlacementSubset d.val (N-d.val)) (b : Bool) :=
  {l : Survivor L x // ∃ j : Fin d.val,
    (exteriorSurvivorEquiv L x hx hb).symm l =
      ⟨d,S,b,if b then j.succ else j.castSucc⟩}

/-- Enumerate exactly each actual interior arm, with multiplicity one. -/
def cyclicArmIndexEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (hx : StrictAnti x)
    (hb : ∀ k, x k ∈ Ioo 0 L) (d : Fin (N+1))
    (S : PlacementSubset d.val (N-d.val)) (b : Bool) :
    Fin d.val ≃ CyclicArm L x hx hb d S b := by
  let e := exteriorSurvivorEquiv L x hx hb
  let p (j : Fin d.val) : ExteriorData N := ⟨d,S,b,if b then j.succ else j.castSucc⟩
  let f (j : Fin d.val) : CyclicArm L x hx hb d S b :=
    ⟨e (p j),j,e.symm_apply_apply (p j)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    have hp := congrArg (fun l : CyclicArm L x hx hb d S b => e.symm l.1) hij
    change e.symm (e (p i)) = e.symm (e (p j)) at hp
    simp only [Equiv.symm_apply_apply] at hp
    have hcut : (if b then i.succ else i.castSucc) =
        (if b then j.succ else j.castSucc) := by
      simpa only [p,Sigma.mk.inj_iff,heq_eq_eq,Prod.mk.injEq,true_and] using hp
    cases b
    · exact Fin.castSucc_injective _ hcut
    · exact Fin.succ_injective _ hcut
  · intro l
    obtain ⟨j,hj⟩ := l.2
    refine ⟨j,Subtype.ext ?_⟩
    apply e.symm.injective
    change e.symm (e (p j)) = e.symm l.1
    rw [Equiv.symm_apply_apply]
    exact hj.symm

/-- Two-sided equivalence on the actual reconstructed exterior labels.
It pairs precisely true cut j+1 with false cut j; endpoints are excluded. -/
def exterior_cyclic_label_equiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (hx : StrictAnti x)
    (hb : ∀ k, x k ∈ Ioo 0 L) (d : Fin (N+1))
    (S : PlacementSubset d.val (N-d.val)) :
    CyclicArm L x hx hb d S true ≃ CyclicArm L x hx hb d S false :=
  (cyclicArmIndexEquiv L x hx hb d S true).symm.trans
    (cyclicArmIndexEquiv L x hx hb d S false)

theorem exterior_cyclic_label_equiv_apply {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (d : Fin (N+1))
    (S : PlacementSubset d.val (N-d.val)) (j : Fin d.val) :
    exterior_cyclic_label_equiv L x hx hb d S
        (cyclicArmIndexEquiv L x hx hb d S true j) =
      cyclicArmIndexEquiv L x hx hb d S false j := by
  simp only [exterior_cyclic_label_equiv,Equiv.trans_apply,Equiv.symm_apply_apply]

/-- The two-sided actual-label equivalence reverses the complete literal
value, with admission and the empty seam profile carried by each label. -/
theorem exterior_cyclic_label_equiv_value {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (d : Fin (N+1)) (S : PlacementSubset d.val (N-d.val)) (j : Fin d.val) :
    value L c n z x (cyclicArmIndexEquiv L x hx hb d S true j).1.1 +
      value L c n z x
        (exterior_cyclic_label_equiv L x hx hb d S
          (cyclicArmIndexEquiv L x hx hb d S true j)).1.1 = 0 := by
  rw [exterior_cyclic_label_equiv_apply]
  change value L c n z x ((exteriorSurvivorEquiv L x hx hb) ⟨d,S,true,j.succ⟩).1 +
    value L c n z x ((exteriorSurvivorEquiv L x hx hb) ⟨d,S,false,j.castSucc⟩).1 = 0
  rw [exteriorSurvivor_value,exteriorSurvivor_value]
  exact exteriorValue_cyclic hL hc hn z x hx hb d S j

/-- Display degree zero separately, without discarding either branch or
introducing a normalization. The positive degrees retain both endpoint families. -/
theorem global_exterior_cyclic_sum_degree_zero {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) :
    let E : Fin (N+1) → ℂ := fun d =>
      ∑ S : PlacementSubset d.val (N-d.val),
        (exteriorValue L c n z x hx hb ⟨d,S,true,0⟩ +
         exteriorValue L c n z x hx hb ⟨d,S,false,Fin.last d.val⟩)
    (∑ p : ExteriorData N, exteriorValue L c n z x hx hb p) =
      E 0 + ∑ d : Fin N, E d.succ := by
  dsimp only
  rw [global_exterior_cyclic_sum hL hc hn z x hx hb]
  exact Fin.sum_univ_succ _

/-- The literal original BGE1 expansion reduces to the two actual endpoint
families, with every original c^m. Pole removal is reserved for spectral assembly. -/
theorem sum_original_eq_endpoint_survivors {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) :
    (∑ d : Fin (N+1), (c : ℂ)^d.val *
      ∑ S : PlacementSubset d.val (N-d.val),
        let X := fun i => x (ambient d (S.1.orderEmbOfFin S.2 i))
        let s := fun j => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) j))
        ∑ T : PlacementSubset d.val (N-d.val),
          (sourceCorners L c (n ∘ ambient d) z X s false T +
           sourceCorners L c (n ∘ ambient d) z X s true T)) =
      ∑ d : Fin (N+1), ∑ S : PlacementSubset d.val (N-d.val),
        (exteriorValue L c n z x hx hb ⟨d,S,true,0⟩ +
         exteriorValue L c n z x hx hb ⟨d,S,false,Fin.last d.val⟩) :=
  (BetheMarkedCancellation.sum_original_eq_exterior hL hc hn z hz x hx hb).trans
    (global_exterior_cyclic_sum hL hc hn z x hx hb)

end QuantumNLS.BetheCyclicGeometry

#print axioms QuantumNLS.BetheCyclicGeometry.exteriorSelected_true_succ
#print axioms QuantumNLS.BetheCyclicGeometry.exteriorSelected_false_castSucc
#print axioms QuantumNLS.BetheCyclicGeometry.paired_branch_displacement
#print axioms QuantumNLS.BetheCyclicGeometry.cutBooleans_succ_update
#print axioms QuantumNLS.BetheCyclicGeometry.paired_orientation
#print axioms QuantumNLS.BetheCyclicGeometry.exteriorChart_strict
#print axioms QuantumNLS.BetheCyclicGeometry.mergeChart_bounds
#print axioms QuantumNLS.BetheCyclicGeometry.antitone_rotate_update_zero
#print axioms QuantumNLS.BetheCyclicGeometry.exterior_true_boundary_rank
#print axioms QuantumNLS.BetheCyclicGeometry.exterior_chart_rotation
#print axioms QuantumNLS.BetheCyclicGeometry.exterior_selected_rank_rotation
#print axioms QuantumNLS.BetheCyclicGeometry.exterior_spectator_rank_rotation
#print axioms QuantumNLS.BetheCyclicGeometry.exterior_pending_rotation
#print axioms QuantumNLS.BetheCyclicGeometry.exterior_merged_rotation
#print axioms QuantumNLS.BetheCyclicGeometry.source_primitive_rotate_boundary
#print axioms QuantumNLS.BetheCyclicGeometry.exterior_chartPrimitive_cyclic
#print axioms QuantumNLS.BetheCyclicGeometry.exterior_chartPrimitive_cyclic_degree
#print axioms QuantumNLS.BetheCyclicGeometry.exteriorValue_cyclic
#print axioms QuantumNLS.BetheCyclicGeometry.sum_exterior_cuts
#print axioms QuantumNLS.BetheCyclicGeometry.global_exterior_cyclic_sum
#print axioms QuantumNLS.BetheCyclicGeometry.CyclicArm
#print axioms QuantumNLS.BetheCyclicGeometry.cyclicArmIndexEquiv
#print axioms QuantumNLS.BetheCyclicGeometry.exterior_cyclic_label_equiv
#print axioms QuantumNLS.BetheCyclicGeometry.exterior_cyclic_label_equiv_apply
#print axioms QuantumNLS.BetheCyclicGeometry.exterior_cyclic_label_equiv_value
#print axioms QuantumNLS.BetheCyclicGeometry.global_exterior_cyclic_sum_degree_zero
#print axioms QuantumNLS.BetheCyclicGeometry.sum_original_eq_endpoint_survivors

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheCyclicGeometry.exteriorSelected_true_succ,
    ``QuantumNLS.BetheCyclicGeometry.exteriorSelected_false_castSucc,
    ``QuantumNLS.BetheCyclicGeometry.paired_branch_displacement,
    ``QuantumNLS.BetheCyclicGeometry.cutBooleans_succ_update,
    ``QuantumNLS.BetheCyclicGeometry.paired_orientation,
    ``QuantumNLS.BetheCyclicGeometry.exteriorChart_strict,
    ``QuantumNLS.BetheCyclicGeometry.mergeChart_bounds,
    ``QuantumNLS.BetheCyclicGeometry.antitone_rotate_update_zero,
    ``QuantumNLS.BetheCyclicGeometry.exterior_true_boundary_rank,
    ``QuantumNLS.BetheCyclicGeometry.exterior_chart_rotation,
    ``QuantumNLS.BetheCyclicGeometry.exterior_selected_rank_rotation,
    ``QuantumNLS.BetheCyclicGeometry.exterior_spectator_rank_rotation,
    ``QuantumNLS.BetheCyclicGeometry.exterior_pending_rotation,
    ``QuantumNLS.BetheCyclicGeometry.exterior_merged_rotation,
    ``QuantumNLS.BetheCyclicGeometry.source_primitive_rotate_boundary,
    ``QuantumNLS.BetheCyclicGeometry.exterior_chartPrimitive_cyclic,
    ``QuantumNLS.BetheCyclicGeometry.exterior_chartPrimitive_cyclic_degree,
    ``QuantumNLS.BetheCyclicGeometry.exteriorValue_cyclic,
    ``QuantumNLS.BetheCyclicGeometry.sum_exterior_cuts,
    ``QuantumNLS.BetheCyclicGeometry.global_exterior_cyclic_sum,
    ``QuantumNLS.BetheCyclicGeometry.CyclicArm,
    ``QuantumNLS.BetheCyclicGeometry.cyclicArmIndexEquiv,
    ``QuantumNLS.BetheCyclicGeometry.exterior_cyclic_label_equiv,
    ``QuantumNLS.BetheCyclicGeometry.exterior_cyclic_label_equiv_apply,
    ``QuantumNLS.BetheCyclicGeometry.exterior_cyclic_label_equiv_value,
    ``QuantumNLS.BetheCyclicGeometry.global_exterior_cyclic_sum_degree_zero,
    ``QuantumNLS.BetheCyclicGeometry.sum_original_eq_endpoint_survivors,

    ``QuantumNLS.BetheMarkedCancellation.sourceRoots_finCongr,
    ``QuantumNLS.BetheMarkedCancellation.cornerSummand_finCongr,
    ``QuantumNLS.BetheMarkedCancellation.cornerSummand_boolean_congr,
    ``QuantumNLS.BetheMarkedCancellation.rawLabel_cornerSummand_transport,
    ``QuantumNLS.BetheMarkedCancellation.exchangeLabel_value,
    ``QuantumNLS.BetheMarkedCancellation.promoteLabel_value,
    ``QuantumNLS.BetheMarkedCancellation.actual_value_triple_balance,
    ``QuantumNLS.BetheMarkedCancellation.marked_fiber_cancellation,
    ``QuantumNLS.BetheMarkedCancellation.global_marked_cancellation,
    ``QuantumNLS.BetheMarkedCancellation.sum_labels_eq_exterior,
    ``QuantumNLS.BetheMarkedCancellation.sum_original_eq_exterior,

    ``QuantumNLS.BetheExteriorMultiplicity.exteriorSurvivor_degree_input,
    ``QuantumNLS.BetheExteriorMultiplicity.exterior_rank_iff,
    ``QuantumNLS.BetheExteriorMultiplicity.extendedOutput_sum,
    ``QuantumNLS.BetheExteriorMultiplicity.exterior_branch_displacement,
    ``QuantumNLS.BetheExteriorMultiplicity.exterior_full_branch_phase,
    ``QuantumNLS.BetheExteriorMultiplicity.exteriorValue,
    ``QuantumNLS.BetheExteriorMultiplicity.exteriorSurvivor_value,
    ``QuantumNLS.BetheExteriorMultiplicity.survivorFiberEquiv,
    ``QuantumNLS.BetheExteriorMultiplicity.noneMarkEquiv,
    ``QuantumNLS.BetheExteriorMultiplicity.sum_noneMark_weighted,
    ``QuantumNLS.BetheExteriorMultiplicity.sum_noneMark_value,
    ``QuantumNLS.BetheExteriorMultiplicity.exteriorRegroupedMark,
    ``QuantumNLS.BetheExteriorMultiplicity.exteriorRegroupedMark_eq,
    ``QuantumNLS.BetheExteriorMultiplicity.sum_exterior_triples_original_weighted,

    ``QuantumNLS.BetheExteriorReconstruction.rectangle_corner_clipping,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorChart,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorChart_sorted,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorChart_unique,
    ``QuantumNLS.BetheExteriorReconstruction.exterior_box,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorBranch,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorBranch_admitted,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorBranch_corner,
    ``QuantumNLS.BetheExteriorReconstruction.ExteriorData,
    ``QuantumNLS.BetheExteriorReconstruction.Survivor,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorRaw,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorRaw_admitted,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorRaw_input,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorRaw_noSeam,
    ``QuantumNLS.BetheExteriorReconstruction.toSurvivor,
    ``QuantumNLS.BetheExteriorReconstruction.survivorCut,
    ``QuantumNLS.BetheExteriorReconstruction.survivorCut_spec,
    ``QuantumNLS.BetheExteriorReconstruction.fromSurvivor,
    ``QuantumNLS.BetheExteriorReconstruction.from_toSurvivor,
    ``QuantumNLS.BetheExteriorReconstruction.to_fromSurvivor,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorSurvivorEquiv,

    ``QuantumNLS.BetheExteriorSurvivors.extendedOutput,
    ``QuantumNLS.BetheExteriorSurvivors.cutBooleans,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_corner,
    ``QuantumNLS.BetheExteriorSurvivors.extendedOutput_strict,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_strict,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_origin,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_rectangle,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_ne_spectator,
    ``QuantumNLS.BetheExteriorSurvivors.exterior_append_injective,
    ``QuantumNLS.BetheExteriorSurvivors.exterior_chart_exists,

    ``QuantumNLS.BetheExteriorCut.rectangle_rise_collision,
    ``QuantumNLS.BetheExteriorCut.rectangle_injective_antitone,
    ``QuantumNLS.BetheExteriorCut.antitone_boolean_cut,
    ``QuantumNLS.BetheExteriorCut.noSeam_boolean_cut,

    ``QuantumNLS.BetheExteriorOrigin.noSeam_iff_injective,
    ``QuantumNLS.BetheExteriorOrigin.noSeam_selected_ne_spectator,
    ``QuantumNLS.BetheExteriorOrigin.noSeam_endpoint_origin,
    ``QuantumNLS.BetheExteriorOrigin.noSeam_coordinates,

    ``QuantumNLS.BetheTripleStrata.seamMark,
    ``QuantumNLS.BetheTripleStrata.FirstLower,
    ``QuantumNLS.BetheTripleStrata.SecondLower,
    ``QuantumNLS.BetheTripleStrata.Higher,
    ``QuantumNLS.BetheTripleStrata.SeamStratum,
    ``QuantumNLS.BetheTripleStrata.lowerEquiv,
    ``QuantumNLS.BetheTripleStrata.raise,
    ``QuantumNLS.BetheTripleStrata.higher_pinned,
    ``QuantumNLS.BetheTripleStrata.higher_demotable,
    ``QuantumNLS.BetheTripleStrata.lower,
    ``QuantumNLS.BetheTripleStrata.higherEquiv,
    ``QuantumNLS.BetheTripleStrata.marked_input_eq,
    ``QuantumNLS.BetheTripleStrata.marked_has_moving,
    ``QuantumNLS.BetheTripleStrata.armEquiv,
    ``QuantumNLS.BetheTripleStrata.tripleEquiv,
    ``QuantumNLS.BetheTripleStrata.lowerEquiv_degree,
    ``QuantumNLS.BetheTripleStrata.higherEquiv_degree,
    ``QuantumNLS.BetheTripleStrata.triple_inputs,
    ``QuantumNLS.BetheTripleStrata.triple_noncollapsed,
    ``QuantumNLS.BetheTripleStrata.sum_triples,
    ``QuantumNLS.BetheTripleStrata.sum_triples_degree,
    ``QuantumNLS.BetheTripleStrata.seamMark_branch,
    ``QuantumNLS.BetheTripleStrata.branchFiberEquiv,
    ``QuantumNLS.BetheTripleStrata.sum_branches,
    ``QuantumNLS.BetheTripleStrata.chosenTripleSum,
    ``QuantumNLS.BetheTripleStrata.sum_chosen_triples,
    ``QuantumNLS.BetheTripleStrata.regroupedMark,
    ``QuantumNLS.BetheTripleStrata.regroupedMark_eq,
    ``QuantumNLS.BetheTripleStrata.sum_marks_triples_original,
    ``QuantumNLS.BetheTripleStrata.sum_regrouped_weighted,
    ``QuantumNLS.BetheTripleStrata.sum_value_weighted,
    ``QuantumNLS.BetheTripleStrata.sum_marks_triples_original_weighted,

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
            throwError "Cyclic geometry nonstandard dependency: {n}"
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
      throwError "Cyclic geometry aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Cyclic geometry aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Cyclic geometry aggregate audit PASS: {seen.size} transitive constants across separate roots. Own cyclic geometry/value/label/sum declarations and inherited BMC1/BEM1/BTS1 physical action and local balance roots audited. Actual exterior cyclic cancellation is proved; spectral assembly has not started."

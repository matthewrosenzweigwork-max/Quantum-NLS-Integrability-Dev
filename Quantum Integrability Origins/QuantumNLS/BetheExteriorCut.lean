import QuantumNLS.BetheExteriorOrigin

/-! Unique Boolean cuts for original none-mark endpoint labels. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheExteriorCut
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport BetheGeneratedLabels BetheSeamProfiles
open BetheSeamReconstruction BetheCrossDegreeReconstruction BetheStrictLabelStrata
open BetheExteriorOrigin
attribute [local instance] Classical.propDecidable

/-- A false/true rise identifies two adjacent original rectangle endpoints
in either branch. -/
theorem rectangle_rise_collision {m : ℕ} (L : ℝ) (X : Fin m → ℝ)
    (b : Bool) (ε : Fin m → Bool) (i : Fin m) (hi : i.val+1 < m)
    (hf : ε i = false) (ht : ε ⟨i.val+1,hi⟩ = true) :
    cornerTuple (rectangleLower X b) (rectangleUpper L X b) ε i =
      cornerTuple (rectangleLower X b) (rectangleUpper L X b) ε ⟨i.val+1,hi⟩ := by
  have hp : 0 < i.val+1 := by omega
  cases b <;> simp [cornerTuple,hf,ht,rectangleLower,rectangleUpper,
    BetheFiniteNAction.lower,BetheFiniteNAction.upper,hi,hp]

/-- Injectivity of the actual rectangle corner excludes every Boolean rise. -/
theorem rectangle_injective_antitone {m : ℕ} (L : ℝ) (X : Fin m → ℝ)
    (b : Bool) (ε : Fin m → Bool)
    (hn : Function.Injective
      (cornerTuple (rectangleLower X b) (rectangleUpper L X b) ε)) :
    Antitone ε := by
  cases m with
  | zero => exact fun i => Fin.elim0 i
  | succ m =>
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    cases hf : ε i.castSucc <;> cases ht : ε i.succ <;> try simp
    have h := hn (rectangle_rise_collision L X b ε i.castSucc
      (by have := i.isLt; simp only [Fin.val_castSucc]; omega) hf ht)
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc] at hv
    omega

/-- Every antitone Boolean word, including the empty one, has a unique cut. -/
theorem antitone_boolean_cut {m : ℕ} (ε : Fin m → Bool) (hε : Antitone ε) :
    ∃! r : Fin (m+1), ∀ i, ε i = true ↔ i.val < r.val := by
  have unique (r s : Fin (m+1))
      (hr : ∀ i, ε i = true ↔ i.val < r.val)
      (hs : ∀ i, ε i = true ↔ i.val < s.val) : r = s := by
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hri : r.val < m := by have := s.isLt; omega
      have he := (hr ⟨r.val,hri⟩).mp ((hs ⟨r.val,hri⟩).mpr h)
      exact (lt_irrefl r.val) he
    · have hsi : s.val < m := by have := r.isLt; omega
      have he := (hs ⟨s.val,hsi⟩).mp ((hr ⟨s.val,hsi⟩).mpr h)
      exact (lt_irrefl s.val) he
  by_cases hn : ∃ i, ε i = false
  · let F := Finset.univ.filter (fun i => ε i = false)
    have hF : F.Nonempty := by
      obtain ⟨i,hi⟩ := hn
      exact ⟨i,by simp [F,hi]⟩
    let j := F.min' hF
    have hj : ε j = false := (Finset.mem_filter.mp (Finset.min'_mem F hF)).2
    let r : Fin (m+1) := ⟨j.val,by have := j.isLt; omega⟩
    have hr (i : Fin m) : ε i = true ↔ i.val < r.val := by
      change ε i = true ↔ i < j
      constructor
      · intro hi
        by_contra h
        have hm := hε (le_of_not_gt h)
        rw [hi,hj] at hm
        exact (by decide : ¬ ((true : Bool) ≤ false)) hm
      · intro hi
        cases he : ε i
        · have hiF : i ∈ F := by simp [F,he]
          exact False.elim ((not_le_of_gt hi) (Finset.min'_le F i hiF))
        · rfl
    exact ⟨r,hr,fun s hs => unique s r hs hr⟩
  · have he (i : Fin m) : ε i = true := by
      cases h : ε i
      · exact False.elim (hn ⟨i,h⟩)
      · rfl
    let r : Fin (m+1) := ⟨m,by omega⟩
    have hr (i : Fin m) : ε i = true ↔ i.val < r.val := by
      simp [he i,r,i.isLt]
    exact ⟨r,hr,fun s hs => unique s r hs hr⟩

/-- Exact unique selected-order cut in every original none-mark label.
No degree-zero or branch exception is suppressed. -/
theorem noSeam_boolean_cut {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (l : RawLabel N) (hn : labelMark L x l = none) :
    ∃! r : Fin (l.1.val+1), ∀ i, l.2.2.2.2 i = true ↔ i.val < r.val := by
  have hc : Function.Injective (coordinates L x l) := by
    intro i j he
    have hh := (noSeam_iff_injective L x l).mp hn
      ((fullInput_selected L x l i).trans (he.trans (fullInput_selected L x l j).symm))
    exact (l.2.1.1.orderEmbOfFin l.2.1.2).injective ((ambient l.1).injective hh)
  rw [noSeam_coordinates L x l hn] at hc
  exact antitone_boolean_cut _ (rectangle_injective_antitone L _ _ _ hc)

end QuantumNLS.BetheExteriorCut

#print axioms QuantumNLS.BetheExteriorCut.rectangle_rise_collision
#print axioms QuantumNLS.BetheExteriorCut.rectangle_injective_antitone
#print axioms QuantumNLS.BetheExteriorCut.antitone_boolean_cut
#print axioms QuantumNLS.BetheExteriorCut.noSeam_boolean_cut
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
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
            throwError "Exterior cut nonstandard dependency: {n}"
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
      throwError "Exterior cut aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Exterior cut aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Exterior cut aggregate audit PASS: {seen.size} transitive constants across separate roots. Exact endpoint provenance and unique Boolean cut proved; exterior reconstruction, global cancellation and spectral assembly remain open."

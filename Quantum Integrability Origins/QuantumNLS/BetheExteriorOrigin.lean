import QuantumNLS.BetheTripleStrata

/-! Exterior endpoint provenance derived from the full none-mark condition. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheExteriorOrigin
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport BetheGeneratedLabels BetheSeamProfiles
open BetheSeamReconstruction BetheCrossDegreeReconstruction BetheStrictLabelStrata
attribute [local instance] Classical.propDecidable

/-- The full none-mark condition is exactly injectivity of the original input. -/
theorem noSeam_iff_injective {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : RawLabel N) :
    labelMark L x l = none ↔ Function.Injective (fullInput L x l) := by
  rw [labelMark, chooseSeam_eq_none]
  constructor
  · intro h i j he
    by_contra hn
    rcases lt_or_gt_of_ne hn with hij | hji
    · have hm := (mem_seams (fullInput L x l) i j).mpr ⟨hij,he⟩
      rw [← labelProfile, h] at hm
      exact Finset.notMem_empty _ hm
    · have hm := (mem_seams (fullInput L x l) j i).mpr ⟨hji,he.symm⟩
      rw [← labelProfile, h] at hm
      exact Finset.notMem_empty _ hm
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨i,j⟩ hm
    obtain ⟨hij,he⟩ := (mem_seams _ i j).mp hm
    exact (ne_of_lt hij) (h he)

/-- A selected endpoint cannot be any literal spectator value. -/
theorem noSeam_selected_ne_spectator {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (l : RawLabel N) (hn : labelMark L x l = none)
    (i : Fin l.1.val) (j : Fin (N-l.1.val)) :
    coordinates L x l i ≠ spectatorTuple x l j := by
  intro he
  have h := (noSeam_iff_injective L x l).mp hn
  have heq := h ((fullInput_selected L x l i).trans
    (he.trans (fullInput_spectator L x l j).symm))
  have hij := (ambient l.1).injective heq
  have hs := l.2.1.1.orderEmbOfFin_mem l.2.1.2 i
  rw [hij] at hs
  exact (Finset.mem_compl.mp
    (l.2.1.1ᶜ.orderEmbOfFin_mem (complement_card l.2.1) j)) hs

/-- The actual chosen endpoint comes from the original rectangle. No
provenance labels, noncollapse premises or cancellation claims are inserted. -/
theorem noSeam_endpoint_origin {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (l : RawLabel N) (hn : labelMark L x l = none) (i : Fin l.1.val) :
    coordinates L x l i =
      if l.2.2.2.2 i then rectangleUpper L (outputTuple x l) l.2.2.2.1 i
      else rectangleLower (outputTuple x l) l.2.2.2.1 i := by
  have hne := noSeam_selected_ne_spectator L x l hn i
  cases he : l.2.2.2.2 i
  · have hc : coordinates L x l i =
        clipLower (outputTuple x l) (spectatorTuple x l) l.2.2.2.1 l.2.2.1 i := by
      simp [coordinates,cornerTuple,he]
    simp only [Bool.false_eq_true,ite_false]
    rcases clipLower_provenance (outputTuple x l) (spectatorTuple x l)
        l.2.2.2.1 l.2.2.1 i with hr | ⟨j,_,hj⟩
    · exact hc.trans hr
    · exact False.elim (hne j (hc.trans hj))
  · have hc : coordinates L x l i =
        clipUpper L (outputTuple x l) (spectatorTuple x l) l.2.2.2.1 l.2.2.1 i := by
      simp [coordinates,cornerTuple,he]
    simp only [ite_true]
    rcases clipUpper_provenance L (outputTuple x l) (spectatorTuple x l)
        l.2.2.2.1 l.2.2.1 i with hr | ⟨j,_,hj⟩
    · exact hc.trans hr
    · exact False.elim (hne j (hc.trans hj))

/-- The whole selected input tuple is the literal unclipped rectangle corner. -/
theorem noSeam_coordinates {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (l : RawLabel N) (hn : labelMark L x l = none) :
    coordinates L x l = cornerTuple
      (rectangleLower (outputTuple x l) l.2.2.2.1)
      (rectangleUpper L (outputTuple x l) l.2.2.2.1) l.2.2.2.2 := by
  funext i
  exact noSeam_endpoint_origin L x l hn i

end QuantumNLS.BetheExteriorOrigin

#print axioms QuantumNLS.BetheExteriorOrigin.noSeam_iff_injective
#print axioms QuantumNLS.BetheExteriorOrigin.noSeam_selected_ne_spectator
#print axioms QuantumNLS.BetheExteriorOrigin.noSeam_endpoint_origin
#print axioms QuantumNLS.BetheExteriorOrigin.noSeam_coordinates
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
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
            throwError "Exterior origin nonstandard dependency: {n}"
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
      throwError "Exterior origin aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Exterior origin aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Exterior origin aggregate audit PASS: {seen.size} transitive constants across separate roots. Actual none-mark endpoint provenance proved; Boolean cut, exterior inverse, global cancellation and spectral assembly remain open."

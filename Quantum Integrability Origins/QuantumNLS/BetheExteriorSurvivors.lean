import QuantumNLS.BetheExteriorCut
import Mathlib.Order.Fin.Tuple

/-! Actual exterior chart reconstruction from a selected subset and cut. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheExteriorSurvivors
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport BetheGeneratedLabels BetheSeamProfiles
open BetheSeamReconstruction BetheCrossDegreeReconstruction BetheStrictLabelStrata
open BetheExteriorOrigin BetheExteriorCut BetheChartFiberSteps
attribute [local instance] Classical.propDecidable

/-- The two endpoint lists, with the actual boundary on its correct side. -/
def extendedOutput {m : ℕ} (L : ℝ) (X : Fin m → ℝ) (b : Bool)
    (k : Fin (m+1)) : ℝ :=
  if b then (if h : 0 < k.val then X ⟨k.val-1,by omega⟩ else L)
  else (if h : k.val < m then X ⟨k.val,h⟩ else 0)

def cutBooleans {m : ℕ} (r : Fin (m+1)) (i : Fin m) : Bool := decide (i.val < r.val)

def exteriorSelected {m : ℕ} (L : ℝ) (X : Fin m → ℝ) (b : Bool)
    (r : Fin (m+1)) : Fin m → ℝ := extendedOutput L X b ∘ r.succAbove

theorem exteriorSelected_corner {m : ℕ} (L : ℝ) (X : Fin m → ℝ)
    (b : Bool) (r : Fin (m+1)) :
    exteriorSelected L X b r =
      cornerTuple (rectangleLower X b) (rectangleUpper L X b) (cutBooleans r) := by
  funext i
  by_cases hi : i.val < r.val
  · rw [exteriorSelected,Function.comp_apply,Fin.succAbove_of_castSucc_lt r i hi]
    cases b <;> simp [extendedOutput,cornerTuple,cutBooleans,hi,
      rectangleUpper,BetheFiniteNAction.upper]
  · rw [exteriorSelected,Function.comp_apply,
      Fin.succAbove_of_le_castSucc r i (by exact le_of_not_gt hi)]
    have hp : 0 < i.val+1 := by omega
    cases b <;> simp [extendedOutput,cornerTuple,cutBooleans,hi,rectangleLower,
      BetheFiniteNAction.lower,hp]

theorem extendedOutput_strict {m : ℕ} (L : ℝ) (X : Fin m → ℝ)
    (hx : StrictAnti X) (hb : ∀ i, X i ∈ Ioo 0 L) (b : Bool) :
    StrictAnti (extendedOutput L X b) := by
  intro i j hij
  have hv : i.val < j.val := hij
  cases b
  · by_cases hj : j.val < m
    · have hi : i.val < m := by omega
      simpa [extendedOutput,hi,hj] using hx (show (⟨i.val,hi⟩ : Fin m) < ⟨j.val,hj⟩ from hij)
    · have hi : i.val < m := by have := j.isLt; omega
      simpa [extendedOutput,hi,hj] using (hb ⟨i.val,hi⟩).1
  · have hj : 0 < j.val := by omega
    by_cases hi : 0 < i.val
    · have h : (⟨i.val-1,by omega⟩ : Fin m) < ⟨j.val-1,by omega⟩ := by
        change i.val-1 < j.val-1; omega
      simpa [extendedOutput,hi,hj] using hx h
    · simpa [extendedOutput,hi,hj] using (hb ⟨j.val-1,by omega⟩).2

theorem exteriorSelected_strict {m : ℕ} (L : ℝ) (X : Fin m → ℝ)
    (hx : StrictAnti X) (hb : ∀ i, X i ∈ Ioo 0 L) (b : Bool) (r : Fin (m+1)) :
    StrictAnti (exteriorSelected L X b r) :=
  (extendedOutput_strict L X hx hb b).comp_strictMono (Fin.strictMono_succAbove r)

/-- Only an actual selected output or the physical boundary can occur. -/
theorem exteriorSelected_origin {m : ℕ} (L : ℝ) (X : Fin m → ℝ)
    (b : Bool) (r : Fin (m+1)) (i : Fin m) :
    exteriorSelected L X b r i = (if b then L else 0) ∨
      ∃ j, exteriorSelected L X b r i = X j := by
  unfold exteriorSelected extendedOutput
  simp only [Function.comp_apply]
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · split_ifs with h
    · exact Or.inr ⟨_,rfl⟩
    · exact Or.inl rfl
  · split_ifs with h
    · exact Or.inr ⟨_,rfl⟩
    · exact Or.inl rfl

theorem exteriorSelected_rectangle {m : ℕ} (L : ℝ) (X : Fin m → ℝ)
    (hx : StrictAnti X) (hb : ∀ i, X i ∈ Ioo 0 L) (b : Bool) (r : Fin (m+1)) :
    exteriorSelected L X b r ∈ closedRectangle L X b := by
  rw [exteriorSelected_corner]
  intro i
  have hl : rectangleLower X b i ≤ rectangleUpper L X b i := by
    cases b
    · exact (BetheFiniteNAction.lower_bounds ⟨hx,hb⟩ i).2.le
    · exact (BetheFiniteNAction.upper_bounds ⟨hx,hb⟩ i).1.le
  cases he : cutBooleans r i <;> simp [cornerTuple,he,hl]

/-- A cut corner and the actual complementary spectators are disjoint. -/
theorem exteriorSelected_ne_spectator {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (b : Bool) (r : Fin (m+1))
    (i : Fin m) (j : Fin q) :
    exteriorSelected L (fun i => x (S.1.orderEmbOfFin S.2 i)) b r i ≠
      x (S.1ᶜ.orderEmbOfFin (complement_card S) j) := by
  intro he
  rcases exteriorSelected_origin L (fun i => x (S.1.orderEmbOfFin S.2 i)) b r i
    with h | ⟨k,h⟩
  · rw [h] at he
    cases b
    · exact (ne_of_gt (hb _).1) he.symm
    · exact (ne_of_lt (hb _).2) he.symm
  · rw [h] at he
    have hk := S.1.orderEmbOfFin_mem S.2 k
    rw [hx.injective he] at hk
    exact (Finset.mem_compl.mp (S.1ᶜ.orderEmbOfFin_mem (complement_card S) j)) hk

/-- Complete selected/spectator input is injective for every cut. -/
theorem exterior_append_injective {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (b : Bool) (r : Fin (m+1)) :
    Function.Injective (Fin.append
      (exteriorSelected L (fun i => x (S.1.orderEmbOfFin S.2 i)) b r)
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j))) := by
  have hX : StrictAnti (fun i => x (S.1.orderEmbOfFin S.2 i)) :=
    fun _ _ h => hx ((S.1.orderEmbOfFin S.2).strictMono h)
  have hs : StrictAnti (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) :=
    fun _ _ h => hx ((S.1ᶜ.orderEmbOfFin (complement_card S)).strictMono h)
  have hY := exteriorSelected_strict L _ hX (fun i => hb _) b r
  intro i j he
  cases i using Fin.addCases <;> cases j using Fin.addCases
  · simp only [Fin.append_left] at he
    exact congrArg (Fin.castAdd q) (hY.injective he)
  · simp only [Fin.append_left,Fin.append_right] at he
    exact False.elim (exteriorSelected_ne_spectator L x hx hb S b r _ _ he)
  · simp only [Fin.append_left,Fin.append_right] at he
    exact False.elim (exteriorSelected_ne_spectator L x hx hb S b r _ _ he.symm)
  · simp only [Fin.append_right] at he
    exact congrArg (Fin.natAdd m) (hs.injective he)


/-- Every subset/branch/cut has exactly one actual merged input chart. -/
theorem exterior_chart_exists {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (b : Bool) (r : Fin (m+1)) :
    ∃! T : PlacementSubset m q,
      Antitone (mergeChart T
        (exteriorSelected L (fun i => x (S.1.orderEmbOfFin S.2 i)) b r)
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j))) := by
  have hX : StrictAnti (fun i => x (S.1.orderEmbOfFin S.2 i)) :=
    fun _ _ h => hx ((S.1.orderEmbOfFin S.2).strictMono h)
  have hs : StrictAnti (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) :=
    fun _ _ h => hx ((S.1ᶜ.orderEmbOfFin (complement_card S)).strictMono h)
  have hY := exteriorSelected_strict L _ hX (fun i => hb _) b r
  apply exists_unique_mergeChart _ _ hY hs
  exact exterior_append_injective L x hx hb S b r
end QuantumNLS.BetheExteriorSurvivors

#print axioms QuantumNLS.BetheExteriorSurvivors.extendedOutput
#print axioms QuantumNLS.BetheExteriorSurvivors.cutBooleans
#print axioms QuantumNLS.BetheExteriorSurvivors.exteriorSelected
#print axioms QuantumNLS.BetheExteriorSurvivors.exteriorSelected_corner
#print axioms QuantumNLS.BetheExteriorSurvivors.extendedOutput_strict
#print axioms QuantumNLS.BetheExteriorSurvivors.exteriorSelected_strict
#print axioms QuantumNLS.BetheExteriorSurvivors.exteriorSelected_origin
#print axioms QuantumNLS.BetheExteriorSurvivors.exteriorSelected_rectangle
#print axioms QuantumNLS.BetheExteriorSurvivors.exteriorSelected_ne_spectator
#print axioms QuantumNLS.BetheExteriorSurvivors.exterior_chart_exists

#print axioms QuantumNLS.BetheExteriorSurvivors.exterior_append_injective

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
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
            throwError "Exterior survivors nonstandard dependency: {n}"
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
      throwError "Exterior survivors aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Exterior survivors aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Exterior survivors aggregate audit PASS: {seen.size} transitive constants across separate roots. Own declarations and inherited BTS1 physical action and local balance roots audited. Global cancellation and spectral assembly remain open."

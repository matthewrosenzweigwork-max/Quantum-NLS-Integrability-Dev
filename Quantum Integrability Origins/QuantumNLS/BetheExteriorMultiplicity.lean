import QuantumNLS.BetheExteriorReconstruction

/-! Literal degree, full phase and exact exterior survivor multiplicity. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheExteriorMultiplicity
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport BetheGeneratedLabels BetheSeamProfiles
open BetheSeamReconstruction BetheCrossDegreeReconstruction BetheStrictLabelStrata
open BetheExteriorOrigin BetheExteriorCut BetheExteriorSurvivors BetheChartFiberSteps
open BetheExteriorReconstruction BethePrimitiveTransport
attribute [local instance] Classical.propDecidable

/-- Literal degree, branch and complete original ambient input are preserved. -/
theorem exteriorSurvivor_degree_input {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (p : ExteriorData N) :
    ((exteriorSurvivorEquiv L x hx hb p).1).1 = p.1 ∧
    ((exteriorSurvivorEquiv L x hx hb p).1).2.1 = p.2.1 ∧
    ((exteriorSurvivorEquiv L x hx hb p).1).2.2.2.1 = p.2.2.1 ∧
    ((exteriorSurvivorEquiv L x hx hb p).1).2.2.2.2 = cutBooleans p.2.2.2 ∧
    fullInput L x (exteriorSurvivorEquiv L x hx hb p).1 =
      mergeChart p.2.1
        (exteriorSelected L (fun i => x (ambient p.1 (p.2.1.1.orderEmbOfFin p.2.1.2 i)))
          p.2.2.1 p.2.2.2)
        (fun j => x (ambient p.1 (p.2.1.1ᶜ.orderEmbOfFin (complement_card p.2.1) j)))
        ∘ (ambient p.1).symm :=
  ⟨rfl,rfl,rfl,rfl,exteriorRaw_input L x hx hb p⟩

/-- Strict input ordering reconstructs the actual selected/spectator rank
comparison; both directions are included. -/
theorem exterior_rank_iff {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (b : Bool) (r : Fin (m+1)) (i : Fin m) (j : Fin q) :
    selectedRank (exteriorChart L x hx hb S b r) i <
      spectatorRank (exteriorChart L x hx hb S b r) j ↔
      x (S.1ᶜ.orderEmbOfFin (complement_card S) j) <
        exteriorSelected L (fun i => x (S.1.orderEmbOfFin S.2 i)) b r i := by
  have hinj := (exterior_append_injective L x hx hb S b r).comp
    (mergePermutation (exteriorChart L x hx hb S b r)).symm.injective
  have hs := (exteriorChart_sorted L x hx hb S b r).strictAnti_of_injective hinj
  have h := hs.lt_iff_gt (a := spectatorRank (exteriorChart L x hx hb S b r) j)
    (b := selectedRank (exteriorChart L x hx hb S b r) i)
  simpa only [mergeChart_selected,mergeChart_spectator] using h.symm

/-- The sum of the branch's extended endpoint list is its full offset. -/
theorem extendedOutput_sum {m : ℕ} (L : ℝ) (X : Fin m → ℝ) (b : Bool) :
    (∑ k : Fin (m+1), extendedOutput L X b k) = branchOffset L X b := by
  cases b
  · rw [Fin.sum_univ_castSucc]
    simp [extendedOutput,branchOffset]
  · rw [Fin.sum_univ_succ]
    simp [extendedOutput,branchOffset]

/-- Telescoping retains the actual boundary phase in both branches. -/
theorem exterior_branch_displacement {m : ℕ} (L : ℝ) (X : Fin m → ℝ)
    (b : Bool) (r : Fin (m+1)) :
    branchOffset L X b - ∑ i, exteriorSelected L X b r i = extendedOutput L X b r := by
  have h := Fin.sum_univ_succAbove (extendedOutput L X b) r
  rw [extendedOutput_sum] at h
  simp only [exteriorSelected,Function.comp_apply]
  linarith

theorem exterior_full_branch_phase {m : ℕ} (L : ℝ) (X : Fin m → ℝ)
    (b : Bool) (r : Fin (m+1)) (z : ℂ) :
    Complex.exp (Complex.I*z*((branchOffset L X b -
      ∑ i, exteriorSelected L X b r i : ℝ) : ℂ)) =
      Complex.exp (Complex.I*z*(extendedOutput L X b r : ℂ)) := by
  rw [exterior_branch_displacement]

/-- Complete literal signed branch contribution, retaining the full branch
phase, source roots, chart primitive and every pending denominator. -/
def exteriorValue {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (z : ℂ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (p : ExteriorData N) : ℂ :=
  let X := fun i => x (ambient p.1 (p.2.1.1.orderEmbOfFin p.2.1.2 i))
  let s := fun j => x (ambient p.1 (p.2.1.1ᶜ.orderEmbOfFin (complement_card p.2.1) j))
  let Y := exteriorSelected L X p.2.2.1 p.2.2.2
  let T := exteriorChart L (x ∘ ambient p.1) (fun _ _ h => hx h)
    (fun _ => hb _) p.2.1 p.2.2.1 p.2.2.2
  (c : ℂ)^p.1.val *
    (orientation (cutBooleans p.2.2.2) *
      Complex.exp (Complex.I*z*((branchOffset L X p.2.2.1 - ∑ i, Y i : ℝ) : ℂ)) *
      chartPrimitive T c (BetheSmooth.sourceRoots L (n ∘ ambient p.1) c)
        Y s z (firstPositions (p := p.1.val) (q := N-p.1.val)))

theorem exteriorSurvivor_value {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (z : ℂ) (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (p : ExteriorData N) :
    value L c n z x (exteriorSurvivorEquiv L x hx hb p).1 =
      exteriorValue L c n z x hx hb p := by
  let X := fun i => x (ambient p.1 (p.2.1.1.orderEmbOfFin p.2.1.2 i))
  let s := fun j => x (ambient p.1 (p.2.1.1ᶜ.orderEmbOfFin (complement_card p.2.1) j))
  let T := exteriorChart L (x ∘ ambient p.1) (fun _ _ h => hx h)
    (fun _ => hb _) p.2.1 p.2.2.1 p.2.2.2
  exact congrArg (fun Y : Fin p.1.val → ℝ =>
    (c : ℂ)^p.1.val *
      (orientation (cutBooleans p.2.2.2) *
        Complex.exp (Complex.I*z*((branchOffset L X p.2.2.1 - ∑ i, Y i : ℝ) : ℂ)) *
        chartPrimitive T c (BetheSmooth.sourceRoots L (n ∘ ambient p.1) c)
          Y s z (firstPositions (p := p.1.val) (q := N-p.1.val))))
    (exteriorBranch_corner L (x ∘ ambient p.1) (fun _ _ h => hx h)
      (fun _ => hb _) p.2.1 p.2.2.1 p.2.2.2)

/-- Flatten proof fields only, into the exact BTS1/BSP1 retained fiber. -/
def survivorFiberEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ) :
    Survivor L x ≃ {l : Label L x // labelMark L x l.1 = none} where
  toFun l := ⟨⟨l.1,l.2.1⟩,l.2.2⟩
  invFun l := ⟨l.1.1,l.1.2,l.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

def noneMarkEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) :
    ExteriorData N ≃ {l : Label L x // labelMark L x l.1 = none} :=
  (exteriorSurvivorEquiv L x hx hb).trans (survivorFiberEquiv L x)

/-- Multiplicity one in each literal degree, for arbitrary weights and values. -/
theorem sum_noneMark_weighted {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (w : ℕ → ℂ) (f : RawLabel N → ℂ) :
    (∑ l : {l : Label L x // labelMark L x l.1 = none}, w l.1.1.1.val * f l.1.1) =
      ∑ p : ExteriorData N, w p.1.val * f (exteriorRaw L x hx hb p) := by
  exact ((noneMarkEquiv L x hx hb).sum_comp
    (fun l => w l.1.1.1.val * f l.1.1)).symm

/-- Exact unchanged none-mark contribution with its full branch phase. -/
theorem sum_noneMark_value {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (z : ℂ) (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (w : ℕ → ℂ) :
    (∑ l : {l : Label L x // labelMark L x l.1 = none},
      w l.1.1.1.val * value L c n z x l.1.1) =
      ∑ p : ExteriorData N, w p.1.val * exteriorValue L c n z x hx hb p := by
  rw [sum_noneMark_weighted L x hx hb w]
  apply Finset.sum_congr rfl
  intro p _
  rw [← exteriorSurvivor_value]
  rfl

/-- Replace precisely the none-mark fiber in BTS1 by the actual exterior sum. -/
def exteriorRegroupedMark {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (w : ℕ → ℂ) (f : RawLabel N → ℂ) (p : Option (Fin N × Fin N)) : ℂ :=
  match p with
  | none => ∑ e : ExteriorData N, w e.1.val * f (exteriorRaw L x hx hb e)
  | some p => BetheTripleStrata.regroupedMark L x hx hb (fun l => w l.1.val * f l) (some p)

theorem exteriorRegroupedMark_eq {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (w : ℕ → ℂ) (f : RawLabel N → ℂ) (p : Option (Fin N × Fin N)) :
    exteriorRegroupedMark L x hx hb w f p =
      BetheTripleStrata.regroupedMark L x hx hb (fun l => w l.1.val * f l) p := by
  cases p with
  | none => exact (sum_noneMark_weighted L x hx hb w f).symm
  | some p => rfl

/-- The complete exterior/triple regrouping equals the literal original
BGE1 sum with exact degree weights and every original c^m. -/
theorem sum_exterior_triples_original_weighted {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (z : ℂ) (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (w : ℕ → ℂ) :
    (∑ p : Option (Fin N × Fin N),
      exteriorRegroupedMark L x hx hb w (value L c n z x) p) =
      ∑ d : Fin (N+1), w d.val * (c : ℂ)^d.val *
        ∑ S : PlacementSubset d.val (N-d.val),
          let X := fun i => x (ambient d (S.1.orderEmbOfFin S.2 i))
          let s := fun j => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) j))
          ∑ T : PlacementSubset d.val (N-d.val),
            (sourceCorners L c (n ∘ ambient d) z X s false T +
             sourceCorners L c (n ∘ ambient d) z X s true T) := by
  simp_rw [exteriorRegroupedMark_eq]
  exact BetheTripleStrata.sum_marks_triples_original_weighted L c n z x hx hb w

end QuantumNLS.BetheExteriorMultiplicity

#print axioms QuantumNLS.BetheExteriorMultiplicity.exteriorSurvivor_degree_input

#print axioms QuantumNLS.BetheExteriorMultiplicity.exterior_rank_iff

#print axioms QuantumNLS.BetheExteriorMultiplicity.extendedOutput_sum

#print axioms QuantumNLS.BetheExteriorMultiplicity.exterior_branch_displacement

#print axioms QuantumNLS.BetheExteriorMultiplicity.exterior_full_branch_phase

#print axioms QuantumNLS.BetheExteriorMultiplicity.exteriorValue

#print axioms QuantumNLS.BetheExteriorMultiplicity.exteriorSurvivor_value

#print axioms QuantumNLS.BetheExteriorMultiplicity.survivorFiberEquiv

#print axioms QuantumNLS.BetheExteriorMultiplicity.noneMarkEquiv

#print axioms QuantumNLS.BetheExteriorMultiplicity.sum_noneMark_weighted

#print axioms QuantumNLS.BetheExteriorMultiplicity.sum_noneMark_value

#print axioms QuantumNLS.BetheExteriorMultiplicity.exteriorRegroupedMark

#print axioms QuantumNLS.BetheExteriorMultiplicity.exteriorRegroupedMark_eq

#print axioms QuantumNLS.BetheExteriorMultiplicity.sum_exterior_triples_original_weighted

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
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
            throwError "Exterior multiplicity nonstandard dependency: {n}"
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
      throwError "Exterior multiplicity aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Exterior multiplicity aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Exterior multiplicity aggregate audit PASS: {seen.size} transitive constants across separate roots. Own declarations and inherited BTS1 physical action and local balance roots audited. Global cancellation and spectral assembly remain open."

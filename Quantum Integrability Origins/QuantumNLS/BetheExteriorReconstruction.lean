import QuantumNLS.BetheExteriorSurvivors

/-! Admission, actual endpoints and complete chart reconstruction for cuts. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheExteriorReconstruction
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport BetheGeneratedLabels BetheSeamProfiles
open BetheSeamReconstruction BetheCrossDegreeReconstruction BetheStrictLabelStrata
open BetheExteriorOrigin BetheExteriorCut BetheExteriorSurvivors BetheChartFiberSteps
attribute [local instance] Classical.propDecidable

/-- Any supported original rectangle corner remains that corner after clipping. -/
theorem rectangle_corner_clipping {m q : ℕ} (L : ℝ) (X : Fin m → ℝ)
    (s : Fin q → ℝ) (b : Bool) (T : PlacementSubset m q) (ε : Fin m → Bool)
    (h : cornerTuple (rectangleLower X b) (rectangleUpper L X b) ε ∈
      Icc (clipLower X s b T) (clipUpper L X s b T)) :
    cornerTuple (clipLower X s b T) (clipUpper L X s b T) ε =
      cornerTuple (rectangleLower X b) (rectangleUpper L X b) ε := by
  funext i
  cases he : ε i
  · have hl := h.1 i
    simp only [cornerTuple,he,Bool.false_eq_true,ite_false] at hl ⊢
    exact le_antisymm hl ((clipLower_le_iff X s b T i _).mp le_rfl).1
  · have hu := h.2 i
    simp only [cornerTuple,he,ite_true] at hu ⊢
    exact le_antisymm ((le_clipUpper_iff L X s b T i _).mp le_rfl).1 hu

def exteriorChart {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (b : Bool) (r : Fin (m+1)) : PlacementSubset m q :=
  Classical.choose (exterior_chart_exists L x hx hb S b r)

theorem exteriorChart_sorted {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (b : Bool) (r : Fin (m+1)) :
    Antitone (mergeChart (exteriorChart L x hx hb S b r)
      (exteriorSelected L (fun i => x (S.1.orderEmbOfFin S.2 i)) b r)
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j))) :=
  (Classical.choose_spec (exterior_chart_exists L x hx hb S b r)).1

theorem exteriorChart_unique {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S T : PlacementSubset m q) (b : Bool) (r : Fin (m+1))
    (ht : Antitone (mergeChart T
      (exteriorSelected L (fun i => x (S.1.orderEmbOfFin S.2 i)) b r)
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)))) :
    T = exteriorChart L x hx hb S b r :=
  (Classical.choose_spec (exterior_chart_exists L x hx hb S b r)).2 T ht

/-- Actual nonempty box, derived for every subset/branch/cut. -/
theorem exterior_box {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (b : Bool) (r : Fin (m+1)) :
    exteriorSelected L (fun i => x (S.1.orderEmbOfFin S.2 i)) b r ∈
      Icc (clipLower (fun i => x (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b
        (exteriorChart L x hx hb S b r))
      (clipUpper L (fun i => x (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b
        (exteriorChart L x hx hb S b r)) := by
  have hX : StrictAnti (fun i => x (S.1.orderEmbOfFin S.2 i)) :=
    fun _ _ h => hx ((S.1.orderEmbOfFin S.2).strictMono h)
  have hs : Antitone (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) :=
    fun _ _ h => hx.antitone ((S.1ᶜ.orderEmbOfFin (complement_card S)).monotone h)
  rw [← closedPhysicalCell_eq_box L _ _ b _ ⟨hX,fun i => hb _⟩ hs
    (fun j => ⟨(hb _).1.le,(hb _).2.le⟩)]
  apply (closedPhysicalCell_iff L _ _ _ b _ ⟨hX,fun i => hb _⟩
    (fun j => ⟨(hb _).1.le,(hb _).2.le⟩)).mpr
  exact ⟨exteriorSelected_rectangle L _ hX (fun i => hb _) b r,
    exteriorChart_sorted L x hx hb S b r⟩

def exteriorBranch {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (b : Bool) (r : Fin (m+1)) : BranchLabel m q :=
  (exteriorChart L x hx hb S b r,b,cutBooleans r)

theorem exteriorBranch_admitted {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (b : Bool) (r : Fin (m+1)) :
    branchAdmitted L (fun i => x (S.1.orderEmbOfFin S.2 i))
      (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j))
      (exteriorBranch L x hx hb S b r) := by
  have h := exterior_box L x hx hb S b r
  exact h.1.trans h.2

theorem exteriorBranch_corner {m q : ℕ} (L : ℝ) (x : Fin (m+q) → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (S : PlacementSubset m q) (b : Bool) (r : Fin (m+1)) :
    cornerTuple
      (clipLower (fun i => x (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b
        (exteriorChart L x hx hb S b r))
      (clipUpper L (fun i => x (S.1.orderEmbOfFin S.2 i))
        (fun j => x (S.1ᶜ.orderEmbOfFin (complement_card S) j)) b
        (exteriorChart L x hx hb S b r)) (cutBooleans r) =
      exteriorSelected L (fun i => x (S.1.orderEmbOfFin S.2 i)) b r := by
  have h := exterior_box L x hx hb S b r
  rw [exteriorSelected_corner] at h ⊢
  exact rectangle_corner_clipping L _ _ b _ _ h


abbrev ExteriorData (N : ℕ) :=
  (d : Fin (N+1)) × PlacementSubset d.val (N-d.val) × Bool × Fin (d.val+1)

abbrev Survivor {N : ℕ} (L : ℝ) (x : Fin N → ℝ) :=
  {l : RawLabel N // admitted L x l ∧ labelMark L x l = none}

/-- Reconstruct the actual original degree, output subset, input chart,
branch and all selected Booleans from exterior data. -/
def exteriorRaw {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (p : ExteriorData N) : RawLabel N :=
  ⟨p.1,p.2.1,exteriorBranch L (x ∘ ambient p.1)
    (fun _ _ h => hx h) (fun _ => hb _) p.2.1 p.2.2.1 p.2.2.2⟩

theorem exteriorRaw_admitted {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (p : ExteriorData N) :
    admitted L x (exteriorRaw L x hx hb p) :=
  exteriorBranch_admitted L (x ∘ ambient p.1) _ _ _ _ _

/-- Complete unsorted input in the original ambient labels. -/
theorem exteriorRaw_input {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (p : ExteriorData N) :
    fullInput L x (exteriorRaw L x hx hb p) =
      mergeChart p.2.1
        (exteriorSelected L (fun i => x (ambient p.1 (p.2.1.1.orderEmbOfFin p.2.1.2 i)))
          p.2.2.1 p.2.2.2)
        (fun j => x (ambient p.1 (p.2.1.1ᶜ.orderEmbOfFin (complement_card p.2.1) j)))
        ∘ (ambient p.1).symm := by
  exact congrArg (fun Y => mergeChart p.2.1 Y
    (fun j => x (ambient p.1 (p.2.1.1ᶜ.orderEmbOfFin (complement_card p.2.1) j)))
      ∘ (ambient p.1).symm)
    (exteriorBranch_corner L (x ∘ ambient p.1)
      (fun _ _ h => hx h) (fun _ => hb _) p.2.1 p.2.2.1 p.2.2.2)

theorem exteriorRaw_noSeam {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (p : ExteriorData N) :
    labelMark L x (exteriorRaw L x hx hb p) = none := by
  apply (noSeam_iff_injective L x _).mpr
  rw [exteriorRaw_input]
  exact ((exterior_append_injective L (x ∘ ambient p.1)
    (fun _ _ h => hx h) (fun _ => hb _) p.2.1 p.2.2.1 p.2.2.2).comp
    (mergePermutation p.2.1).symm.injective).comp (ambient p.1).symm.injective

def toSurvivor {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (p : ExteriorData N) : Survivor L x :=
  ⟨exteriorRaw L x hx hb p,exteriorRaw_admitted L x hx hb p,
    exteriorRaw_noSeam L x hx hb p⟩

def survivorCut {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : Survivor L x) :
    Fin (l.1.1.val+1) := Classical.choose (noSeam_boolean_cut L x l.1 l.2.2)

theorem survivorCut_spec {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : Survivor L x) :
    ∀ i, l.1.2.2.2.2 i = true ↔ i.val < (survivorCut L x l).val :=
  (Classical.choose_spec (noSeam_boolean_cut L x l.1 l.2.2)).1

def fromSurvivor {N : ℕ} (L : ℝ) (x : Fin N → ℝ) (l : Survivor L x) : ExteriorData N :=
  ⟨l.1.1,l.1.2.1,l.1.2.2.2.1,survivorCut L x l⟩

/-- Exterior extraction recovers the cut uniquely, including degree zero. -/
theorem from_toSurvivor {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (p : ExteriorData N) :
    fromSurvivor L x (toSurvivor L x hx hb p) = p := by
  have hr : survivorCut L x (toSurvivor L x hx hb p) = p.2.2.2 := by
    apply Eq.symm
    apply (Classical.choose_spec
      (noSeam_boolean_cut L x (toSurvivor L x hx hb p).1
        (toSurvivor L x hx hb p).2.2)).2
    intro i
    simp [toSurvivor,exteriorRaw,exteriorBranch,cutBooleans]
  rcases p with ⟨d,S,b,r⟩
  change (⟨d,S,b,survivorCut L x (toSurvivor L x hx hb ⟨d,S,b,r⟩)⟩ : ExteriorData N) = _
  rw [hr]

/-- Every admitted none-mark label reconstructs its actual original chart
and every Boolean. No survivor is inferred merely from an empty mixed profile. -/
theorem to_fromSurvivor {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) (l : Survivor L x) :
    toSurvivor L x hx hb (fromSurvivor L x l) = l := by
  rcases l with ⟨⟨d,S,T,b,ε⟩,ha,hn⟩
  let l : Survivor L x := ⟨⟨d,S,T,b,ε⟩,ha,hn⟩
  let r := survivorCut L x l
  have he : ε = cutBooleans r := by
    funext i
    rw [Bool.eq_iff_iff]
    simpa only [cutBooleans,decide_eq_true_eq] using survivorCut_spec L x l i
  have hc := noSeam_coordinates L x (⟨d,S,T,b,ε⟩ : RawLabel N) hn
  change coordinates L x (⟨d,S,T,b,ε⟩ : RawLabel N) =
    cornerTuple (rectangleLower (outputTuple x ⟨d,S,T,b,ε⟩) b)
      (rectangleUpper L (outputTuple x ⟨d,S,T,b,ε⟩) b) ε at hc
  conv_rhs at hc => rw [he,← exteriorSelected_corner]
  have hX : StrictAnti (fun i => x (ambient d (S.1.orderEmbOfFin S.2 i))) :=
    fun _ _ h => hx ((S.1.orderEmbOfFin S.2).strictMono h)
  have hs : Antitone (fun j => x (ambient d (S.1ᶜ.orderEmbOfFin (complement_card S) j))) :=
    fun _ _ h => hx.antitone ((S.1ᶜ.orderEmbOfFin (complement_card S)).monotone h)
  have hbox : coordinates L x (⟨d,S,T,b,ε⟩ : RawLabel N) ∈
      Icc (clipLower (outputTuple x ⟨d,S,T,b,ε⟩) (spectatorTuple x ⟨d,S,T,b,ε⟩) b T)
        (clipUpper L (outputTuple x ⟨d,S,T,b,ε⟩) (spectatorTuple x ⟨d,S,T,b,ε⟩) b T) :=
    cornerTuple_mem_box _ _ ha ε
  have hcell := (closedPhysicalCell_eq_box L _ _ b T ⟨hX,fun i => hb _⟩ hs
    (fun j => ⟨(hb _).1.le,(hb _).2.le⟩)).symm ▸ hbox
  have hsorted := hcell.2.1
  rw [hc] at hsorted
  have ht : T = exteriorChart L (x ∘ ambient d)
      (fun _ _ h => hx h) (fun _ => hb _) S b r :=
    exteriorChart_unique L (x ∘ ambient d) _ _ S T b r hsorted
  apply Subtype.ext
  change (⟨d,S,exteriorBranch L (x ∘ ambient d) _ _ S b r⟩ : RawLabel N) = ⟨d,S,T,b,ε⟩
  apply congrArg (fun br : BranchLabel d.val (N-d.val) => (⟨d,S,br⟩ : RawLabel N))
  exact Prod.ext ht.symm (Prod.ext rfl he.symm)

/-- Actual two-sided subset/branch/cut correspondence with all original
none-mark chart/rank/domain/endpoint labels. -/
def exteriorSurvivorEquiv {N : ℕ} (L : ℝ) (x : Fin N → ℝ)
    (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) : ExteriorData N ≃ Survivor L x where
  toFun := toSurvivor L x hx hb
  invFun := fromSurvivor L x
  left_inv := from_toSurvivor L x hx hb
  right_inv := to_fromSurvivor L x hx hb

end QuantumNLS.BetheExteriorReconstruction

#print axioms QuantumNLS.BetheExteriorReconstruction.rectangle_corner_clipping

#print axioms QuantumNLS.BetheExteriorReconstruction.exteriorChart

#print axioms QuantumNLS.BetheExteriorReconstruction.exteriorChart_sorted

#print axioms QuantumNLS.BetheExteriorReconstruction.exteriorChart_unique

#print axioms QuantumNLS.BetheExteriorReconstruction.exterior_box

#print axioms QuantumNLS.BetheExteriorReconstruction.exteriorBranch

#print axioms QuantumNLS.BetheExteriorReconstruction.exteriorBranch_admitted

#print axioms QuantumNLS.BetheExteriorReconstruction.exteriorBranch_corner

#print axioms QuantumNLS.BetheExteriorReconstruction.ExteriorData

#print axioms QuantumNLS.BetheExteriorReconstruction.Survivor

#print axioms QuantumNLS.BetheExteriorReconstruction.exteriorRaw

#print axioms QuantumNLS.BetheExteriorReconstruction.exteriorRaw_admitted

#print axioms QuantumNLS.BetheExteriorReconstruction.exteriorRaw_input

#print axioms QuantumNLS.BetheExteriorReconstruction.exteriorRaw_noSeam

#print axioms QuantumNLS.BetheExteriorReconstruction.toSurvivor

#print axioms QuantumNLS.BetheExteriorReconstruction.survivorCut

#print axioms QuantumNLS.BetheExteriorReconstruction.survivorCut_spec

#print axioms QuantumNLS.BetheExteriorReconstruction.fromSurvivor

#print axioms QuantumNLS.BetheExteriorReconstruction.from_toSurvivor

#print axioms QuantumNLS.BetheExteriorReconstruction.to_fromSurvivor

#print axioms QuantumNLS.BetheExteriorReconstruction.exteriorSurvivorEquiv

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
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
            throwError "Exterior reconstruction nonstandard dependency: {n}"
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
      throwError "Exterior reconstruction aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Exterior reconstruction aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Exterior reconstruction aggregate audit PASS: {seen.size} transitive constants across separate roots. Own declarations and inherited BTS1 physical action and local balance roots audited. Global cancellation and spectral assembly remain open."

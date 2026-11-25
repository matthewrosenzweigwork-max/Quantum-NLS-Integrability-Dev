import QuantumNLS.BetheExteriorMultiplicity

/-! Literal all-degree value transport and cancellation of actual marked triples. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheMarkedCancellation
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheGeneratedEndpoints BetheNeighborPromotion
open BetheInputAdjacency BetheCornerTransport BetheGeneratedLabels BetheSeamProfiles
open BetheSeamReconstruction BetheCrossDegreeReconstruction BetheStrictLabelStrata
open BetheTripleStrata
attribute [local instance] Classical.propDecidable

/-- Pure ambient equality transports the actual source roots, without a
permutation or an assumption about the chosen variational solution. -/
theorem sourceRoots_finCongr {M N : ℕ} (h : M = N) (L c : ℝ) (n : Fin N → ℤ) :
    BetheSmooth.sourceRoots L (n ∘ finCongr h) c =
      BetheSmooth.sourceRoots L n c ∘ finCongr h := by
  subst N
  rfl

/-- Transport every factor of the signed physical summand together. -/
theorem cornerSummand_finCongr {M N : ℕ} (h : M = N) (L c : ℝ)
    (r : Fin N → ℝ) (z : ℂ) (x : Fin N → ℝ)
    (A : Finset (Fin N)) (π : Equiv.Perm (Fin N)) (b : Bool) (ε : Fin N → Bool) :
    cornerSummand L c (r ∘ finCongr h) z (x ∘ finCongr h)
      (A.map (finCongr h).symm.toEmbedding)
      ((finCongr h).trans (π.trans (finCongr h).symm)) b (ε ∘ finCongr h) =
      cornerSummand L c r z x A π b ε := by
  subst N
  simp

/-- Spectator Boolean extensions have no effect on the literal summand. -/
theorem cornerSummand_boolean_congr {N : ℕ} (L c : ℝ) (r : Fin N → ℝ)
    (z : ℂ) (x : Fin N → ℝ) (A : Finset (Fin N)) (π : Equiv.Perm (Fin N))
    (b : Bool) (ε δ : Fin N → Bool) (he : ∀ k ∈ A, ε k = δ k) :
    cornerSummand L c r z x A π b ε = cornerSummand L c r z x A π b δ := by
  have hv : physicalCorner L x A π b ε = physicalCorner L x A π b δ := by
    funext k
    by_cases hk : k ∈ A
    · simp only [physicalCorner,hk,ite_true,he k hk]
    · simp only [physicalCorner,hk,ite_false]
  have hs : physicalOrientation A ε = physicalOrientation A δ := by
    unfold physicalOrientation
    apply Finset.prod_congr rfl
    intro k hk
    rw [he k hk]
  simp only [cornerSummand,hv,hs]

/-- Every admitted original label, in every degree including 0 and N,
retains the exact c^m, full phase, orientation, roots and pending denominators. -/
theorem rawLabel_cornerSummand_transport {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (z : ℂ) (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (hl : admitted L x l) :
    value L c n z x l = cornerSummand L c (BetheSmooth.sourceRoots L n c) z x
      (outputSet l) (ordering l) l.2.2.2.1 (booleans l) := by
  have hx' : StrictAnti (x ∘ ambient l.1) := fun _ _ h => hx h
  have hcell := label_cell L x hx hb l hl
  have hcell' := (cell_transport (M := l.1.val+(N-l.1.val)) (by omega)
    L x (fullInput L x l) (outputSet l) (ordering l) l.2.2.2.1).mpr hcell
  change physicalCell L (x ∘ ambient l.1)
    ((outputSet l).map (ambient l.1).symm.toEmbedding)
    ((ambient l.1).trans ((ordering l).trans (ambient l.1).symm))
    l.2.2.2.1 (fullInput L x l ∘ ambient l.1) at hcell'
  rw [outputSet_pullback,ordering_pullback] at hcell'
  have hv := cornerSummand_eq_actual L c
    (BetheSmooth.sourceRoots L (n ∘ ambient l.1) c) z (x ∘ ambient l.1)
    (fullInput L x l ∘ ambient l.1) hx' (fun _ => hb _) l.2.1 l.2.2.1
    l.2.2.2.1 hcell' (branchExtension l.2.1 l.2.2)
  simp only [branchExtension_selected] at hv
  have hv' : cornerSummand L c (BetheSmooth.sourceRoots L (n ∘ ambient l.1) c) z
      (x ∘ ambient l.1) l.2.1.1 (inputOrdering l.2.1 l.2.2.1)
      l.2.2.2.1 (branchExtension l.2.1 l.2.2) = value L c n z x l := by
    refine hv.trans ?_
    unfold BetheGeneratedLabels.value BetheGeneratedLabels.branchValue
      BetheGeneratedLabels.outputTuple BetheGeneratedLabels.spectatorTuple
    dsimp only
    simp only [Function.comp_apply,mul_assoc]
  rw [← hv']
  have ht := cornerSummand_finCongr (M := l.1.val+(N-l.1.val)) (by omega)
    L c (BetheSmooth.sourceRoots L n c) z x (outputSet l) (ordering l)
    l.2.2.2.1 (booleans l)
  change cornerSummand L c (BetheSmooth.sourceRoots L n c ∘ ambient l.1) z
    (x ∘ ambient l.1) ((outputSet l).map (ambient l.1).symm.toEmbedding)
    ((ambient l.1).trans ((ordering l).trans (ambient l.1).symm))
    l.2.2.2.1 (booleans l ∘ ambient l.1) = _ at ht
  rw [outputSet_pullback,ordering_pullback] at ht
  have he : booleans l ∘ ambient l.1 = branchExtension l.2.1 l.2.2 := by
    funext k
    simp only [booleans,Function.comp_apply,Equiv.symm_apply_apply]
  rw [he] at ht
  have hr := sourceRoots_finCongr (M := l.1.val+(N-l.1.val)) (by omega) L c n
  change BetheSmooth.sourceRoots L (n ∘ ambient l.1) c =
    BetheSmooth.sourceRoots L n c ∘ ambient l.1 at hr
  rw [hr]
  exact ht

/-- The actual exchange transports its entire signed value to the second
physical corner; no chart or Boolean label is supplied separately. -/
theorem exchangeLabel_value {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (z : ℂ) (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (a t : Fin N) (ha : a ∈ outputSet l)
    (hp : orderedBlocks (outputSet l) (exchangedOrdering (ordering l) a t))
    (hl : admitted L x (exchangeLabel l a t hp)) :
    value L c n z x (exchangeLabel l a t hp) =
      cornerSummand L c (BetheSmooth.sourceRoots L n c) z x (outputSet l)
        (exchangedOrdering (ordering l) a t) l.2.2.2.1
        (Function.update (booleans l) a (!(booleans l a))) := by
  rw [rawLabel_cornerSummand_transport L c n z x hx hb _ hl,
    (exchangeLabel_data l a t hp).1,(exchangeLabel_data l a t hp).2.1,
    (exchangeLabel_data l a t hp).2.2,exchangeLabel_booleans l a t ha hp]

/-- Promotion retains every Boolean on the enlarged selected set; its
literal degree and all primitive denominators are handled by the general transport. -/
theorem promoteLabel_value {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (z : ℂ) (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (l : RawLabel N) (t : Fin N)
    (hp : orderedBlocks (insert t (outputSet l)) (ordering l))
    (hl : admitted L x (promoteLabel l t hp)) :
    value L c n z x (promoteLabel l t hp) =
      cornerSummand L c (BetheSmooth.sourceRoots L n c) z x (insert t (outputSet l))
        (ordering l) l.2.2.2.1 (Function.update (booleans l) t (!l.2.2.2.1)) := by
  rw [rawLabel_cornerSummand_transport L c n z x hx hb _ hl,
    (promoteLabel_data l t hp).1,(promoteLabel_data l t hp).2.1,
    (promoteLabel_data l t hp).2.2]
  apply cornerSummand_boolean_congr
  intro k hk
  simp only [promoteLabel,reconstruct_booleans,hk,ite_true]

/-- Full literal value balance on the three original BTS1 arms, with
positive-c roots and their actual antiderivative nonpole condition. -/
theorem actual_value_triple_balance {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (a t : Fin N) (b : Bool) (ho : if b then t < a else a < t)
    (l : FirstLower L x a t b) :
    value L c n z x l.1.1 +
      value L c n z x (lowerEquiv L x hx hb a t b l).1.1 +
      value L c n z x (higherEquiv L x hx hb a t b ho l).1 = 0 := by
  let A := outputSet l.1.1
  let π := ordering l.1.1
  let ε := Function.update (booleans l.1.1) t (!b)
  have hat : a ≠ t := fun h => l.1.2.2.2.2.1 (h ▸ l.1.2.2.2.1)
  have hp := (mixed_incident_iff L x hx hb l.1.1 l.1.2.1 a t
    l.1.2.2.2.1 l.1.2.2.2.2.1 l.1.2.2.2.2.2).mpr (l.2.2.trans l.2.1.symm)
  have hy := label_cell L x hx hb l.1.1 l.1.2.1
  have hg := collision_internalGap L x _ hx _ a t _ hy.1
    l.1.2.2.2.1 l.1.2.2.2.2.1 l.1.2.2.2.2.2
  have hbal := source_generated_corner_balance hL hc hn x (fullInput L x l.1.1) hx
    (fun k => ⟨(hb k).1.le,(hb k).2.le⟩) A a t l.1.1.2.2.2.1 hg
    l.1.2.2.2.2.2 π hp hy z hz ε
    (by simpa only [ε,Function.update_of_ne hat] using l.2.2.trans l.2.1.symm)
    (by simp only [ε,Function.update_self,l.2.1])
  have hfirst : value L c n z x l.1.1 =
      cornerSummand L c (BetheSmooth.sourceRoots L n c) z x A π b ε := by
    rw [rawLabel_cornerSummand_transport L c n z x hx hb _ l.1.2.1,l.2.1]
    apply cornerSummand_boolean_congr
    intro k hk
    have hkt : k ≠ t := fun h => l.1.2.2.2.2.1 (h ▸ hk)
    simp only [ε,Function.update_of_ne hkt]
  have hsecond : value L c n z x (lowerEquiv L x hx hb a t b l).1.1 =
      cornerSummand L c (BetheSmooth.sourceRoots L n c) z x A
        (exchangedOrdering π a t) b (Function.update ε a (!b)) := by
    let hpE := label_exchanged_chart L x hx hb l.1.1 l.1.2.1 a t
      l.1.2.2.2.1 l.1.2.2.2.2.1 l.1.2.2.2.2.2
    change value L c n z x (exchangeLabel l.1.1 a t hpE) = _
    rw [exchangeLabel_value L c n z x hx hb _ a t l.1.2.2.2.1 hpE
      (lowerEquiv L x hx hb a t b l).1.2.1,l.2.1,l.2.2]
    apply cornerSummand_boolean_congr
    intro k hk
    by_cases hka : k = a
    · subst k; simp only [Function.update_self]
    · have hkt : k ≠ t := fun h => l.1.2.2.2.2.1 (h ▸ hk)
      simp only [ε,Function.update_of_ne hka,Function.update_of_ne hkt]
  have hthird : value L c n z x (higherEquiv L x hx hb a t b ho l).1 =
      cornerSummand L c (BetheSmooth.sourceRoots L n c) z x (insert t A) π b ε := by
    change value L c n z x (promoteLabel l.1.1 t hp) = _
    rw [promoteLabel_value L c n z x hx hb _ t hp
      (higherEquiv L x hx hb a t b ho l).2.1,l.2.1]
  rw [hfirst,hsecond,hthird]
  simpa only [l.2.1] using hbal

/-- Exhaustive triple cancellation inside one chosen full-profile mark.
The invalid unordered-mark fiber is empty by its actual definition. -/
theorem marked_fiber_cancellation {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L)
    (p : Fin N × Fin N) :
    (∑ l : {l : Label L x // labelMark L x l.1 = some p},
      value L c n z x l.1.1) = 0 := by
  rw [← regroupedMark_eq L x hx hb (value L c n z x) (some p)]
  by_cases hp : p.1 < p.2
  · simp only [regroupedMark,dite_eq_left hp,chosenTripleSum]
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro l _
    exact actual_value_triple_balance hL hc hn z hz x hx hb _ _ b
      (by cases b <;> simpa using hp) l
  · simp only [regroupedMark,dite_eq_right hp]

/-- The disjoint union of all actual marked fibers has zero total value. -/
theorem global_marked_cancellation {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) :
    (∑ p : Fin N × Fin N,
      ∑ l : {l : Label L x // labelMark L x l.1 = some p},
        value L c n z x l.1.1) = 0 := by
  simp_rw [marked_fiber_cancellation hL hc hn z hz x hx hb]
  exact Finset.sum_const_zero

/-- The original admitted sum equals the actual reconstructed exterior
sum after, and only after, the proved global marked cancellation. -/
theorem sum_labels_eq_exterior {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (x : Fin N → ℝ) (hx : StrictAnti x) (hb : ∀ k, x k ∈ Ioo 0 L) :
    (∑ l : Label L x, value L c n z x l.1) =
      ∑ p : BetheExteriorReconstruction.ExteriorData N,
        BetheExteriorMultiplicity.exteriorValue L c n z x hx hb p := by
  rw [← sum_marks]
  rw [Fintype.sum_option,global_marked_cancellation hL hc hn z hz x hx hb,add_zero]
  simpa only [one_mul] using
    BetheExteriorMultiplicity.sum_noneMark_value L c n z x hx hb (fun _ => 1)

/-- Exact original BGE1 expansion with every c^m, now reduced to actual
exterior labels. No arbitrary degree weight is asserted to cancel. -/
theorem sum_original_eq_exterior {N : ℕ} {L c : ℝ}
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
      ∑ p : BetheExteriorReconstruction.ExteriorData N,
        BetheExteriorMultiplicity.exteriorValue L c n z x hx hb p := by
  rw [← sum_value]
  exact sum_labels_eq_exterior hL hc hn z hz x hx hb

end QuantumNLS.BetheMarkedCancellation

#print axioms QuantumNLS.BetheMarkedCancellation.sourceRoots_finCongr

#print axioms QuantumNLS.BetheMarkedCancellation.cornerSummand_finCongr

#print axioms QuantumNLS.BetheMarkedCancellation.cornerSummand_boolean_congr

#print axioms QuantumNLS.BetheMarkedCancellation.rawLabel_cornerSummand_transport

#print axioms QuantumNLS.BetheMarkedCancellation.exchangeLabel_value

#print axioms QuantumNLS.BetheMarkedCancellation.promoteLabel_value

#print axioms QuantumNLS.BetheMarkedCancellation.actual_value_triple_balance

#print axioms QuantumNLS.BetheMarkedCancellation.marked_fiber_cancellation

#print axioms QuantumNLS.BetheMarkedCancellation.global_marked_cancellation

#print axioms QuantumNLS.BetheMarkedCancellation.sum_labels_eq_exterior

#print axioms QuantumNLS.BetheMarkedCancellation.sum_original_eq_exterior

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
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
            throwError "Marked cancellation nonstandard dependency: {n}"
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
      throwError "Marked cancellation aggregate missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.TransferSeparation" ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Marked cancellation aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Marked cancellation aggregate audit PASS: {seen.size} transitive constants across separate roots. Own declarations and inherited BEM1/BTS1 physical action and local balance roots audited. Actual all-degree marked cancellation is proved; exterior cyclic transport and spectral assembly remain open."

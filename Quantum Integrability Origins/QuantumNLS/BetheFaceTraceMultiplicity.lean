import QuantumNLS.BetheRectangleIncidence

/-! Boundary parameter measures, not an inference from the volume-a.e.
chamber partition. Insert one fixed face value and integrate the remaining
coordinates with ordinary mass-L cube measure. Exceptional additional
collisions/endpoints are proved null for that face parameter measure. -/
noncomputable section
open MeasureTheory Set
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheFaceTraceMultiplicity
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts BetheRectangleIncidence
open BetheWeakGradient

/-- If only one coordinate is allowed to be at a rectangle endpoint,
all moving coordinates remain strictly ordered. Thus moving/moving
collision faces occur only at intersections of rectangle endpoint faces. -/
theorem strictAnti_of_other_interior {r : ℕ} (L : ℝ) (X y : Fin (r+1) → ℝ)
    (b : Bool) (a : Fin (r+1)) (hy : y ∈ closedRectangle L X b)
    (ho : ∀ k, k ≠ a → y k ∈ Ioo (rectangleLower X b k) (rectangleUpper L X b k)) :
    StrictAnti y := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro j
  have hne : j.castSucc ≠ j.succ := by intro h; have := congrArg Fin.val h; simp at this
  cases b
  · have hj : j.val+1 < r+1 := by omega
    have hl : X j.succ ≤ y j.castSucc := by
      have hh := (hy j.castSucc).1
      simp only [rectangleLower,Bool.false_eq_true,ite_false,BetheFiniteNAction.lower,
        Fin.val_castSucc,dite_eq_left hj] at hh
      exact hh
    have hu : y j.succ ≤ X j.succ := (hy j.succ).2
    by_cases ha : j.castSucc = a
    · have hja : j.succ ≠ a := fun h => hne (ha.trans h.symm)
      exact (ho j.succ hja).2.trans_le hl
    · have hl' : X j.succ < y j.castSucc := by
        have hh := (ho j.castSucc ha).1
        simp only [rectangleLower,Bool.false_eq_true,ite_false,BetheFiniteNAction.lower,
          Fin.val_castSucc,dite_eq_left hj] at hh
        exact hh
      exact hu.trans_lt hl'
  · have hj : 0 < j.succ.val := by simp
    have hl : X j.castSucc ≤ y j.castSucc := (hy j.castSucc).1
    have hu : y j.succ ≤ X j.castSucc := by
      have hh := (hy j.succ).2
      simp only [rectangleUpper,ite_true,BetheFiniteNAction.upper,dite_eq_left hj] at hh
      exact hh
    by_cases ha : j.castSucc = a
    · have hja : j.succ ≠ a := fun h => hne (ha.trans h.symm)
      have hu' : y j.succ < X j.castSucc := by
        have hh := (ho j.succ hja).2
        simp only [rectangleUpper,ite_true,BetheFiniteNAction.upper,dite_eq_left hj] at hh
        exact hh
      exact hu'.trans_le hl
    · exact hu.trans_lt (ho j.castSucc ha).1

/-- On each actual coordinate face, all other coordinates are strictly
inside their intervals almost everywhere in the face parameter measure. -/
theorem face_ae_other_interior {r : ℕ} (L : ℝ) (X : Fin (r+1) → ℝ) (b : Bool)
    (a : Fin (r+1)) (v : ℝ) :
    ∀ᵐ u ∂cubeMeasure r L,
      let y := Fin.insertNth (α := fun _ => ℝ) a v u
      y ∈ closedRectangle L X b →
        ∀ k, k ≠ a → y k ∈ Ioo (rectangleLower X b k) (rectangleUpper L X b k) := by
  filter_upwards [cube_ae_cross_ne L (rectangleLower X b),cube_ae_cross_ne L (rectangleUpper L X b)]
    with u hl hu
  dsimp only
  intro hy k
  refine Fin.succAboveCases a ?_ (fun j => ?_) k
  · intro h; exact False.elim (h rfl)
  · intro _
    have hk := hy (a.succAbove j)
    simp only [Fin.insertNth_apply_succAbove] at hk ⊢
    exact ⟨lt_of_le_of_ne hk.1 (hl j (a.succAbove j)).symm,
      lt_of_le_of_ne hk.2 (hu j (a.succAbove j))⟩

theorem face_ae_strictAnti {r : ℕ} (L : ℝ) (X : Fin (r+1) → ℝ) (b : Bool)
    (a : Fin (r+1)) (v : ℝ) :
    ∀ᵐ u ∂cubeMeasure r L,
      let y := Fin.insertNth (α := fun _ => ℝ) a v u
      y ∈ closedRectangle L X b → StrictAnti y := by
  filter_upwards [face_ae_other_interior L X b a v] with u hu
  dsimp only
  intro hy
  exact strictAnti_of_other_interior L X _ b a hy (hu hy)

/-- A face fixed away from spectator values has no mixed collision almost
everywhere in its own parameter measure. -/
theorem face_ae_noCollision {r q : ℕ} (L : ℝ) (s : Fin q → ℝ)
    (a : Fin (r+1)) (v : ℝ) (hv : ∀ j, v ≠ s j) :
    ∀ᵐ u ∂cubeMeasure r L,
      ∀ k j, Fin.insertNth (α := fun _ => ℝ) a v u k ≠ s j := by
  filter_upwards [cube_ae_cross_ne L s] with u hu
  intro k j
  refine Fin.succAboveCases a ?_ (fun l => ?_) k
  · simpa only [Fin.insertNth_apply_same] using hv j
  · simpa only [Fin.insertNth_apply_succAbove] using hu l j

/-- A spectator face has exactly the displayed mixed collision almost
everywhere; all additional mixed collisions are null on that face. -/
theorem face_ae_singleCollision {r q : ℕ} (L : ℝ) (s : Fin q → ℝ)
    (hs : StrictAnti s) (a : Fin (r+1)) (j : Fin q) :
    ∀ᵐ u ∂cubeMeasure r L,
      singleCollision (Fin.insertNth (α := fun _ => ℝ) a (s j) u) s a j := by
  filter_upwards [cube_ae_cross_ne L s] with u hu
  refine ⟨by simp,?_⟩
  intro k l
  refine Fin.succAboveCases a ?_ (fun t => ?_) k
  · intro he
    exact ⟨rfl,hs.injective (by simpa only [Fin.insertNth_apply_same] using he.symm)⟩
  · intro he
    exact False.elim (hu t l (by simpa only [Fin.insertNth_apply_succAbove] using he))

/-- Actual rectangle endpoint trace: chart multiplicity one almost
everywhere on the face, conditional only on belonging to the rectangle. -/
theorem rectangle_face_multiplicity_ae {r q : ℕ} (L : ℝ) (x : Fin ((r+1)+q) → ℝ)
    (hx : x ∈ BetheWavefunctions.chamber ((r+1)+q) L)
    (S : PlacementSubset (r+1) q) (b : Bool) (f : RectangleFace (r+1)) :
    let X := fun i => x (selectedRank S i)
    let s := fun j => x (spectatorRank S j)
    ∀ᵐ u ∂cubeMeasure r L,
      let y := Fin.insertNth (α := fun _ => ℝ) f.1 (rectangleEndpoint L X b f) u
      y ∈ closedRectangle L X b → (incidentCharts y s).card = 1 := by
  dsimp only
  let X := fun i => x (selectedRank S i)
  let s := fun j => x (spectatorRank S j)
  have hs : StrictAnti s := by
    intro i j hij
    apply hx.1
    simpa only [spectatorRank,mergePermutation_spectator] using
      (S.1ᶜ.orderEmbOfFin (complement_card S)).strictMono hij
  filter_upwards [face_ae_strictAnti L X b f.1 (rectangleEndpoint L X b f),
    face_ae_noCollision L s f.1 (rectangleEndpoint L X b f)
      (physical_endpoint_ne_spectator L x hx S b f)] with u hu hn
  intro hy
  exact card_noCollision_charts _ s (hu hy) hs hn

/-- Actual spectator face trace: exactly two adjacent chart incidences
almost everywhere in the residual cube measure. -/
theorem spectator_face_multiplicity_ae {r q : ℕ} (L : ℝ) (X : Fin (r+1) → ℝ)
    (s : Fin q → ℝ) (hs : StrictAnti s) (b : Bool) (a : Fin (r+1)) (j : Fin q) :
    ∀ᵐ u ∂cubeMeasure r L,
      let y := Fin.insertNth (α := fun _ => ℝ) a (s j) u
      y ∈ closedRectangle L X b →
        (incidentCharts y s).card = 2 ∧
        ∀ S, y ∈ chartSet S s →
          (spectatorRank S j).val = (selectedRank S a).val+1 ∨
            (selectedRank S a).val = (spectatorRank S j).val+1 := by
  filter_upwards [face_ae_strictAnti L X b a (s j),face_ae_singleCollision L s hs a j]
    with u hu hc
  dsimp only
  intro hy
  exact ⟨card_singleCollision_charts _ s (hu hy) hs a j hc,
    fun S hS => singleCollision_adjacent _ s (hu hy) hs a j hc S hS⟩

end QuantumNLS.BetheFaceTraceMultiplicity

#print axioms QuantumNLS.BetheFaceTraceMultiplicity.strictAnti_of_other_interior
#print axioms QuantumNLS.BetheFaceTraceMultiplicity.face_ae_other_interior
#print axioms QuantumNLS.BetheFaceTraceMultiplicity.face_ae_strictAnti
#print axioms QuantumNLS.BetheFaceTraceMultiplicity.face_ae_noCollision
#print axioms QuantumNLS.BetheFaceTraceMultiplicity.face_ae_singleCollision
#print axioms QuantumNLS.BetheFaceTraceMultiplicity.rectangle_face_multiplicity_ae
#print axioms QuantumNLS.BetheFaceTraceMultiplicity.spectator_face_multiplicity_ae

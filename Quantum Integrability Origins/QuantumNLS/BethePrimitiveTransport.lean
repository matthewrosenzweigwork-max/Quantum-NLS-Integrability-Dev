import QuantumNLS.BetheFaceTraceMultiplicity

/-! The actual two-chart seam transports every previously integrated input
label. The BIF1 identity then applies to the two literal primitive traces,
with multiplicity one per incidence and no orbit factor. These local
identities do not identify all iterated physical integral boundary terms. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BethePrimitiveTransport
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts
open BetheRectangleIncidence BetheInternalFaces BetheCrossDegreeFaces

def activeRanks {m q : ℕ} (S : PlacementSubset m q) (A : Finset (Fin (m+q))) :
    Finset (Fin (m+q)) := A.image (mergePermutation S)

def chartPrimitive {m q : ℕ} (S : PlacementSubset m q) (c : ℝ)
    (r : Fin (m+q) → ℝ) (y : Fin m → ℝ) (s : Fin q → ℝ) (z : ℂ)
    (A : Finset (Fin (m+q))) : ℂ :=
  primitive c r (mergeChart S y s) z (activeRanks S A)

theorem activeRanks_insert {m q : ℕ} (S : PlacementSubset m q)
    (A : Finset (Fin (m+q))) (a : Fin (m+q)) :
    activeRanks S (insert a A) = insert (mergePermutation S a) (activeRanks S A) := by
  classical
  exact Finset.image_insert _ _ _

theorem rank_notMem {m q : ℕ} (S : PlacementSubset m q)
    (A : Finset (Fin (m+q))) (a : Fin (m+q)) (ha : a ∉ A) :
    mergePermutation S a ∉ activeRanks S A := by
  classical
  intro h
  obtain ⟨k,hk,he⟩ := Finset.mem_image.mp h
  exact ha ((mergePermutation S).injective he ▸ hk)

/-- Every pending denominator label is transported through the actual
chart change; labels away from the collision are unchanged in rank. -/
theorem activeRanks_face {m q : ℕ} (S T : PlacementSubset m q)
    (i : Fin m) (j : Fin q)
    (hT : mergePermutation T = mergePermutation S * Equiv.swap (Fin.castAdd q i) (Fin.natAdd m j))
    (A : Finset (Fin (m+q))) (ha : Fin.castAdd q i ∉ A) (hb : Fin.natAdd m j ∉ A) :
    activeRanks T A = activeRanks S A := by
  classical
  apply Finset.image_congr
  intro k hk
  have hka : k ≠ Fin.castAdd q i := fun h => ha (h ▸ hk)
  have hkb : k ≠ Fin.natAdd m j := fun h => hb (h ▸ hk)
  simp [hT,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hka hkb]

theorem face_rank_swap {m q : ℕ} (S T : PlacementSubset m q) (i : Fin m) (j : Fin q)
    (hT : mergePermutation T = mergePermutation S * Equiv.swap (Fin.castAdd q i) (Fin.natAdd m j)) :
    selectedRank T i = spectatorRank S j ∧ spectatorRank T j = selectedRank S i := by
  simp [selectedRank,spectatorRank,hT,Equiv.Perm.mul_apply]

/-- Choose the orientation in which the moving input lies immediately
above the spectator in the first chart. Both charts are actual incidences. -/
theorem oriented_singleCollision_charts {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) (i : Fin m) (j : Fin q)
    (hc : singleCollision y s i j) :
    ∃ S T : PlacementSubset m q, S ≠ T ∧ y ∈ chartSet S s ∧ y ∈ chartSet T s ∧
      (spectatorRank S j).val = (selectedRank S i).val+1 ∧
      mergePermutation T = mergePermutation S * Equiv.swap (Fin.castAdd q i) (Fin.natAdd m j) ∧
      (∀ U, y ∈ chartSet U s ↔ U = S ∨ U = T) := by
  classical
  obtain ⟨S,T,hne,hST,hperm⟩ := singleCollision_charts y s hy hs i j hc
  have hS := (hST S).mpr (Or.inl rfl)
  have hT := (hST T).mpr (Or.inr rfl)
  rcases singleCollision_adjacent y s hy hs i j hc S hS with h | h
  · exact ⟨S,T,hne,hS,hT,h,hperm,hST⟩
  · refine ⟨T,S,hne.symm,hT,hS,?_,?_,?_⟩
    · rw [(face_rank_swap S T i j hperm).1,(face_rank_swap S T i j hperm).2]
      exact h
    · rw [hperm,Equiv.mul_swap_mul_self]
    · intro U
      rw [hST U,or_comm]

/-- The first chart meets the seam as a lower coordinate endpoint;
the second meets it as an upper endpoint. Thus ordinary interval evaluation
has exactly the T-minus-S orientation used in source_chart_seam. -/
theorem face_halfspaces {m q : ℕ} (S T : PlacementSubset m q) (i : Fin m) (j : Fin q)
    (s : Fin q → ℝ)
    (hadj : (spectatorRank S j).val = (selectedRank S i).val+1)
    (hperm : mergePermutation T = mergePermutation S * Equiv.swap (Fin.castAdd q i) (Fin.natAdd m j)) :
    (∀ y, y ∈ chartSet S s → s j ≤ y i) ∧
      (∀ y, y ∈ chartSet T s → y i ≤ s j) := by
  have hr : selectedRank S i ≤ spectatorRank S j := by
    apply Fin.le_iff_val_le_val.mpr
    omega
  constructor
  · intro y hy
    exact (((chartSet_iff S y s).mp hy).2.2 i j).1 hr
  · intro y hy
    apply (((chartSet_iff T y s).mp hy).2.2 i j).2
    rw [(face_rank_swap S T i j hperm).1,(face_rank_swap S T i j hperm).2]
    exact hr

/-- The BIF1 recurrence on two actual chart traces, with the entire active
set derived from original integration labels. The displayed adjacency is
proved by oriented_singleCollision_charts for any simple mixed collision. -/
theorem source_chart_seam {m q : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (m+q) → ℤ} (hn : Antitone n) (y : Fin m → ℝ) (s : Fin q → ℝ)
    (i : Fin m) (j : Fin q) (he : y i = s j) (S T : PlacementSubset m q)
    (hS : y ∈ chartSet S s) (hT : y ∈ chartSet T s)
    (hadj : (spectatorRank S j).val = (selectedRank S i).val+1)
    (hperm : mergePermutation T = mergePermutation S * Equiv.swap (Fin.castAdd q i) (Fin.natAdd m j))
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (A : Finset (Fin (m+q))) (ha : Fin.castAdd q i ∉ A) (hb : Fin.natAdd m j ∉ A) :
    chartPrimitive T c (BetheSmooth.sourceRoots L n c) y s z (insert (Fin.castAdd q i) A) -
      chartPrimitive S c (BetheSmooth.sourceRoots L n c) y s z (insert (Fin.castAdd q i) A) =
      (c : ℂ) * chartPrimitive S c (BetheSmooth.sourceRoots L n c) y s z
        (insert (Fin.castAdd q i) (insert (Fin.natAdd m j) A)) := by
  have hx : mergeChart S y s (selectedRank S i) = mergeChart S y s (spectatorRank S j) := by
    simpa only [mergeChart_selected,mergeChart_spectator] using he
  have hf := source_primitive_internal_face hL hc hn (mergeChart S y s) z hz
    (activeRanks S A) hadj (rank_notMem S A _ ha) (rank_notMem S A _ hb) hx
  unfold chartPrimitive
  rw [← chart_trace_eq S T y s hS hT]
  simp only [activeRanks_insert]
  rw [activeRanks_face S T i j hperm A ha hb]
  change primitive c _ (mergeChart S y s) z (insert (selectedRank T i) (activeRanks S A)) - _ = _
  rw [(face_rank_swap S T i j hperm).1]
  exact hf

/-- A further ordinary integration across one face with an arbitrary
previously integrated denominator set. All endpoint terms are retained. -/
theorem integral_primitive_crossing {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) (x : Fin N → ℝ) (a b : Fin N)
    (hadj : b.val = a.val+1) (he : x a = x b) (z : ℂ)
    (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ))
    (A : Finset (Fin N)) (ha : a ∉ A) (hb : b ∉ A) (u lo hi : ℝ) :
    (∫ t in lo..x a, Complex.exp (Complex.I*z*(u-t)) *
      primitive c (BetheSmooth.sourceRoots L n c) (Function.update x b t) z A) +
    (∫ t in x a..hi, Complex.exp (Complex.I*z*(u-t)) *
      primitive c (BetheSmooth.sourceRoots L n c) (Function.update x a t) z A) =
    Complex.exp (Complex.I*z*(u-hi)) *
      primitive c (BetheSmooth.sourceRoots L n c) (Function.update x a hi) z (insert a A) -
    Complex.exp (Complex.I*z*(u-lo)) *
      primitive c (BetheSmooth.sourceRoots L n c) (Function.update x b lo) z (insert b A) +
    (c : ℂ) * Complex.exp (Complex.I*z*(u-x a)) *
      primitive c (BetheSmooth.sourceRoots L n c) x z (insert a (insert b A)) := by
  have h1 := integral_primitive_update c (BetheSmooth.sourceRoots L n c) x b z hz A hb u lo (x a)
  have h2 := integral_primitive_update c (BetheSmooth.sourceRoots L n c) x a z hz A ha u (x a) hi
  have hua : Function.update x a (x a) = x := Function.update_eq_self a x
  have hub : Function.update x b (x a) = x := by rw [he]; exact Function.update_eq_self b x
  rw [hub] at h1
  rw [hua] at h2
  rw [h1,h2]
  have hf := source_primitive_internal_face hL hc hn x z hz A hadj ha hb he
  linear_combination Complex.exp (Complex.I*z*(u-x a)) * hf

/-- The local primitive seam identity on almost every point of an actual
rectangle spectator face. Geometry and chart orientation are conclusions;
no primitive matching or cancellation identity is a hypothesis. -/
theorem source_spectator_face_seam_ae {r q : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin ((r+1)+q) → ℤ} (hn : Antitone n) (X : Fin (r+1) → ℝ)
    (s : Fin q → ℝ) (hs : StrictAnti s) (b : Bool) (a : Fin (r+1)) (j : Fin q)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ)) :
    ∀ᵐ u ∂BetheWeakGradient.cubeMeasure r L,
      let y := Fin.insertNth (α := fun _ => ℝ) a (s j) u
      y ∈ closedRectangle L X b →
      ∃ S T : PlacementSubset (r+1) q, S ≠ T ∧ y ∈ chartSet S s ∧ y ∈ chartSet T s ∧
        (incidentCharts y s).card = 2 ∧
        ∀ A : Finset (Fin ((r+1)+q)), Fin.castAdd q a ∉ A → Fin.natAdd (r+1) j ∉ A →
          chartPrimitive T c (BetheSmooth.sourceRoots L n c) y s z (insert (Fin.castAdd q a) A) -
            chartPrimitive S c (BetheSmooth.sourceRoots L n c) y s z (insert (Fin.castAdd q a) A) =
          (c : ℂ) * chartPrimitive S c (BetheSmooth.sourceRoots L n c) y s z
            (insert (Fin.castAdd q a) (insert (Fin.natAdd (r+1) j) A)) := by
  filter_upwards [BetheFaceTraceMultiplicity.face_ae_strictAnti L X b a (s j),
    BetheFaceTraceMultiplicity.face_ae_singleCollision L s hs a j] with u hu hcollision
  dsimp only
  intro hrect
  have hy := hu hrect
  obtain ⟨S,T,hne,hS,hT,hadj,hperm,_⟩ :=
    oriented_singleCollision_charts _ s hy hs a j hcollision
  refine ⟨S,T,hne,hS,hT,card_singleCollision_charts _ s hy hs a j hcollision,?_⟩
  intro A ha hb
  exact source_chart_seam hL hc hn _ s a j (by simp) S T hS hT hadj hperm z hz A ha hb

end QuantumNLS.BethePrimitiveTransport

#print axioms QuantumNLS.BethePrimitiveTransport.activeRanks
#print axioms QuantumNLS.BethePrimitiveTransport.chartPrimitive
#print axioms QuantumNLS.BethePrimitiveTransport.activeRanks_insert
#print axioms QuantumNLS.BethePrimitiveTransport.rank_notMem
#print axioms QuantumNLS.BethePrimitiveTransport.activeRanks_face
#print axioms QuantumNLS.BethePrimitiveTransport.face_rank_swap
#print axioms QuantumNLS.BethePrimitiveTransport.oriented_singleCollision_charts
#print axioms QuantumNLS.BethePrimitiveTransport.face_halfspaces
#print axioms QuantumNLS.BethePrimitiveTransport.source_chart_seam
#print axioms QuantumNLS.BethePrimitiveTransport.integral_primitive_crossing
#print axioms QuantumNLS.BethePrimitiveTransport.source_spectator_face_seam_ae

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BethePrimitiveTransport.source_spectator_face_seam_ae,
    ``QuantumNLS.BethePrimitiveTransport.integral_primitive_crossing,
    ``QuantumNLS.BethePrimitiveTransport.face_halfspaces,
    ``QuantumNLS.BetheFaceTraceMultiplicity.rectangle_face_multiplicity_ae,
    ``QuantumNLS.BetheFaceTraceMultiplicity.spectator_face_multiplicity_ae,
    ``QuantumNLS.BetheRectangleIncidence.closedCell_iff,
    ``QuantumNLS.BetheRectangleIncidence.closedCell_interior_or_face,
    ``QuantumNLS.BetheRectangleIncidence.card_cellFace,
    ``QuantumNLS.BethePhysicalFaceCharts.source_transferTerm_charts_ae]
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
  for n in #[``QuantumNLS.BetheRectangleIncidence.singleCollision_charts,
      ``QuantumNLS.BetheRectangleIncidence.card_singleCollision_charts,
      ``QuantumNLS.BetheRectangleIncidence.singleCollision_adjacent,
      ``QuantumNLS.BetheRectangleIncidence.chart_trace_eq,
      ``QuantumNLS.BetheRectangleIncidence.physical_endpoint_ne_spectator,
      ``QuantumNLS.BetheFaceTraceMultiplicity.face_ae_other_interior,
      ``QuantumNLS.BetheFaceTraceMultiplicity.face_ae_noCollision,
      ``QuantumNLS.BetheFaceTraceMultiplicity.face_ae_singleCollision,
      ``QuantumNLS.BethePrimitiveTransport.activeRanks_face,
      ``QuantumNLS.BethePrimitiveTransport.source_chart_seam,
      ``QuantumNLS.BetheInternalFaces.source_primitive_internal_face,
      ``QuantumNLS.BetheCrossDegreeFaces.integral_primitive_update,
      ``QuantumNLS.BethePhysicalReindex.source_transferTerm_raw_ae,
      ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
      ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "Rectangle incidence aggregate audit missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Rectangle incidence aggregate audit forbidden dependency: {n}"
  Lean.logInfo m!"Rectangle incidence aggregate audit PASS: {seen.size} transitive constants across the listed roots; frozen actual physical transfer normalization plus original-face boundary measures, exact one/two chart incidences, signs, pending denominator transport and local primitive seam. This aggregate audit does not assert a derivation of global cancellation or eigenrelation."

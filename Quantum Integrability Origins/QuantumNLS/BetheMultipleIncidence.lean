import QuantumNLS.BetheCyclicPrimitives
import Mathlib.GroupTheory.Perm.DomMulAct

/-! Exact merged-chart multiplicity at any number of simultaneous mixed
collisions, provided each input block is strictly ordered. This extends the
original simple-face count pointwise to intersections. It is not the
successive physical integration recurrence, and does not discard corners
where the moving block itself has repeated values. -/
noncomputable section
open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheMultipleIncidence
open TensorPlacements BetheFaceEnumeration BethePhysicalFaceCharts BetheRectangleIncidence

/-- Compare any incident chart with a fixed incident chart. Their relative
permutation preserves every original input value, including all collisions. -/
def incidentToStabilizer {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (S : PlacementSubset m q) (hS : y ∈ chartSet S s)
    (T : {T : PlacementSubset m q // y ∈ chartSet T s}) :
    {π : Equiv.Perm (Fin (m+q)) // Fin.append y s ∘ π = Fin.append y s} :=
  ⟨(mergePermutation S).symm * mergePermutation T.1, by
    ext i
    have he := congrFun (chart_trace_eq S T.1 y s hS T.2) (mergePermutation T.1 i)
    simpa only [mergeChart, Function.comp_apply, Equiv.Perm.mul_apply,
      Equiv.symm_apply_apply] using he⟩

/-- With strict order inside each block, every value-preserving permutation
produces one actual merged chart, and no two produce the same chart. -/
theorem incidentToStabilizer_bijective {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) (S : PlacementSubset m q)
    (hS : y ∈ chartSet S s) : Function.Bijective (incidentToStabilizer y s S hS) := by
  classical
  constructor
  · intro T U he
    have hp := congrArg Subtype.val he
    have ht : mergePermutation T.1 = mergePermutation U.1 := by
      change (mergePermutation S).symm * mergePermutation T.1 =
        (mergePermutation S).symm * mergePermutation U.1 at hp
      exact mul_left_cancel hp
    apply Subtype.ext
    exact (mergePermutation_image T.1).symm.trans
      ((congrArg (placementSubsetOfPerm (p := m) (q := q)) ht).trans (mergePermutation_image U.1))
  · intro π
    let τ := mergePermutation S * π.1
    have hτ : Antitone (Fin.append y s ∘ τ.symm) := by
      have he : Fin.append y s ∘ τ.symm = Fin.append y s ∘ (mergePermutation S).symm := by
        ext i
        change Fin.append y s (π.1.symm ((mergePermutation S).symm i)) = _
        have h := congrFun π.2 (π.1.symm ((mergePermutation S).symm i))
        simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h.symm
      rw [he]
      exact hS
    let T := placementSubsetOfPerm (p := m) (q := q) τ
    have hp : mergePermutation T = τ := (sorting_perm_merge y s hy hs τ hτ).symm
    have hT : y ∈ chartSet T s := by
      change Antitone (Fin.append y s ∘ (mergePermutation T).symm)
      rw [hp]
      exact hτ
    refine ⟨⟨T,hT⟩,?_⟩
    apply Subtype.ext
    change (mergePermutation S).symm * mergePermutation T = π.1
    rw [hp]
    apply Equiv.ext
    intro i
    change (mergePermutation S).symm (mergePermutation S (π.1 i)) = π.1 i
    exact (mergePermutation S).symm_apply_apply _

/-- Full factorial fiber formula. Every incident chart is counted exactly
once, without assuming independent seam choices or an orbit multiplicity. -/
theorem card_incidentCharts {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) :
    (incidentCharts y s).card =
      ∏ v ∈ Finset.univ.image (Fin.append y s),
        (Fintype.card {i : Fin (m+q) // Fin.append y s i = v}).factorial := by
  classical
  obtain ⟨S,hS⟩ := exists_mergeChart y s hy hs
  have he := Fintype.card_congr
    (Equiv.ofBijective (incidentToStabilizer y s S hS)
      (incidentToStabilizer_bijective y s hy hs S hS))
  rw [DomMulAct.stabilizer_card'] at he
  simpa only [Fintype.card_subtype, incidentCharts] using he

/-- A value fiber of two strictly ordered blocks has at most two labels.
The equality remains pointwise at simultaneous mixed intersections. -/
theorem append_fiber_card_le_two {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) (v : ℝ) :
    Fintype.card {i : Fin (m+q) // Fin.append y s i = v} ≤ 2 := by
  classical
  let tag : {i : Fin (m+q) // Fin.append y s i = v} → Bool :=
    fun i => decide (i.1.val < m)
  have hi : Function.Injective tag := by
    intro a b he
    apply Subtype.ext
    obtain ⟨a,ha⟩ := a
    obtain ⟨b,hb⟩ := b
    revert ha hb he
    refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) b <;> intro ha hb he
    · exact congrArg (Fin.castAdd q) (hy.injective ((show y i = v by simpa using ha).trans (show v = y j by simpa using hb.symm)))
    · have ht : tag ⟨Fin.castAdd q i,ha⟩ = true := by simp [tag]
      have hf : tag ⟨Fin.natAdd m j,hb⟩ = false := by simp [tag]
      rw [ht,hf] at he
      contradiction
    · have ht : tag ⟨Fin.castAdd q j,hb⟩ = true := by simp [tag]
      have hf : tag ⟨Fin.natAdd m i,ha⟩ = false := by simp [tag]
      rw [hf,ht] at he
      contradiction
    · exact congrArg (Fin.natAdd m) (hs.injective ((show s i = v by simpa using ha).trans (show v = s j by simpa using hb.symm)))
  simpa using Fintype.card_le_of_injective tag hi

/-- A double value is precisely one moving label and one spectator label;
strictness excludes repeated labels inside either block. -/
theorem append_fiber_card_eq_two_iff {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) (v : ℝ) :
    Fintype.card {i : Fin (m+q) // Fin.append y s i = v} = 2 ↔
      ∃ i j, y i = v ∧ s j = v := by
  classical
  constructor
  · intro hc
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩,hne⟩ := Fintype.exists_pair_of_one_lt_card (by omega :
      1 < Fintype.card {i : Fin (m+q) // Fin.append y s i = v})
    have hab : a ≠ b := fun h => hne (Subtype.ext h)
    clear hne
    revert ha hb hab
    refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) b <;> intro ha hb hab
    · exact False.elim (hab (congrArg (Fin.castAdd q)
        (hy.injective ((show y i = v by simpa using ha).trans (show v = y j by simpa using hb.symm)))))
    · exact ⟨i,j,by simpa using ha,by simpa using hb⟩
    · exact ⟨j,i,by simpa using hb,by simpa using ha⟩
    · exact False.elim (hab (congrArg (Fin.natAdd m)
        (hs.injective ((show s i = v by simpa using ha).trans (show v = s j by simpa using hb.symm)))))
  · rintro ⟨i,j,hi,hj⟩
    have hne : (Fin.castAdd q i : Fin (m+q)) ≠ Fin.natAdd m j := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    have hc : 1 < Fintype.card {k : Fin (m+q) // Fin.append y s k = v} :=
      Fintype.one_lt_card_iff.mpr ⟨⟨Fin.castAdd q i,by simpa using hi⟩,
        ⟨Fin.natAdd m j,by simpa using hj⟩,fun h => hne (congrArg Subtype.val h)⟩
    have hle := append_fiber_card_le_two y s hy hs v
    omega

/-- Number of distinct double-valued fibers, not a count of nondegenerate
facets. It includes all simultaneous mixed collisions of strict blocks. -/
def doubleValues {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ.image (Fin.append y s)).filter
    (fun v => Fintype.card {i : Fin (m+q) // Fin.append y s i = v} = 2)

/-- Exact higher-intersection multiplicity: k distinct mixed collision
values give 2^k charts, by the complete stabilizer classification. -/
theorem card_incidentCharts_pow {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) :
    (incidentCharts y s).card = 2 ^ (doubleValues y s).card := by
  classical
  rw [card_incidentCharts y s hy hs]
  have hf (v : ℝ) :
      (Fintype.card {i : Fin (m+q) // Fin.append y s i = v}).factorial =
        if Fintype.card {i : Fin (m+q) // Fin.append y s i = v} = 2 then 2 else 1 := by
    have h := append_fiber_card_le_two y s hy hs v
    interval_cases hcard : Fintype.card {i : Fin (m+q) // Fin.append y s i = v} <;> decide
  simp_rw [hf]
  rw [Finset.prod_ite]
  simp [doubleValues]

/-- The exponent counts actual common moving/spectator values. -/
theorem doubleValues_eq_inter {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) :
    doubleValues y s = Finset.univ.image y ∩ Finset.univ.image s := by
  classical
  ext v
  simp only [doubleValues,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,
    append_fiber_card_eq_two_iff y s hy hs,Finset.mem_inter]
  constructor
  · rintro ⟨_,i,j,hi,hj⟩
    exact ⟨⟨i,hi⟩,⟨j,hj⟩⟩
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩⟩
    exact ⟨⟨Fin.castAdd q i,by simpa using hi⟩,i,j,hi,hj⟩

theorem card_incidentCharts_mixed_intersections {m q : ℕ} (y : Fin m → ℝ) (s : Fin q → ℝ)
    (hy : StrictAnti y) (hs : StrictAnti s) :
    (incidentCharts y s).card = 2 ^ (Finset.univ.image y ∩ Finset.univ.image s).card := by
  rw [card_incidentCharts_pow y s hy hs,doubleValues_eq_inter y s hy hs]

end QuantumNLS.BetheMultipleIncidence

#print axioms QuantumNLS.BetheMultipleIncidence.incidentToStabilizer
#print axioms QuantumNLS.BetheMultipleIncidence.incidentToStabilizer_bijective
#print axioms QuantumNLS.BetheMultipleIncidence.card_incidentCharts
#print axioms QuantumNLS.BetheMultipleIncidence.append_fiber_card_le_two
#print axioms QuantumNLS.BetheMultipleIncidence.doubleValues
#print axioms QuantumNLS.BetheMultipleIncidence.card_incidentCharts_pow

#print axioms QuantumNLS.BetheMultipleIncidence.append_fiber_card_eq_two_iff
#print axioms QuantumNLS.BetheMultipleIncidence.doubleValues_eq_inter
#print axioms QuantumNLS.BetheMultipleIncidence.card_incidentCharts_mixed_intersections

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheMultipleIncidence.card_incidentCharts_mixed_intersections,
    ``QuantumNLS.BetheCyclicPrimitives.integral_source_primitive_outer_pair,
    ``QuantumNLS.BetheCyclicPrimitives.integral_source_primitive_outer_cancel,
    ``QuantumNLS.BethePrimitiveTransport.source_spectator_face_seam_ae,
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
  for n in #[``QuantumNLS.BetheCyclicPrimitives.denominator_relabel,
      ``QuantumNLS.BetheCyclicPrimitives.rotateActive,
      ``QuantumNLS.BethePeriodic.sourceRoots_term_periodic,
      ``QuantumNLS.BetheMultipleIncidence.incidentToStabilizer_bijective,
      ``DomMulAct.stabilizer_card',
      ``QuantumNLS.BetheCrossDegreeFaces.integral_primitive_update,
      ``QuantumNLS.BetheInternalFaces.source_primitive_internal_face,
      ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
      ``QuantumNLS.BetheSmooth.sourceRoots] do
    unless seen.contains n do
      throwError "Cyclic/multiple incidence aggregate audit missing ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Cyclic/multiple incidence aggregate audit forbidden dependency: {n}"
  Lean.logInfo m!"Cyclic/multiple incidence aggregate audit PASS: {seen.size} transitive constants across separate roots for new cyclic primitives and multiple intersections, frozen BRI1 local seams and BPR1 physical chart action. This aggregate does not derive the complete integration recurrence, global cancellation or eigenrelation."

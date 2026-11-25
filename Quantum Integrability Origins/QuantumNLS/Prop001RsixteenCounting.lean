import QuantumNLS.Prop001RfifteenFinite

/-! Literal subset-fiber counting for the finite marginal hierarchy. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
open scoped BigOperators ENNReal InnerProductSpace
namespace QuantumNLS.Prop001RsixteenCounting
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementFusion PlacementGrouping
  PlacementOverlap PlacementUnionReindex PlacementFiberTransport PhysicalEnergyTrace
  Ext025A12Trace Ext025A12Normal Ext025A12PartialTrace Ext025A12Collision
  Prop001 Prop001RfourteenRegrouping Prop001RfourteenTraceRegrouping
  Prop001RfifteenTransport Prop001RfifteenRemainder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Original placement coordinates and literal Fin N subset coordinates agree. -/
theorem castSlotSet_eq_map {a b : ℕ} (h : a=b) (S : Finset (Fin a)) :
    castSlotSet h S = S.map (finCongr h).toEmbedding := by
  cases h
  rfl

/-- The original setPlacement really is the original raw subset operator. -/
theorem setPlacement_slots (N r : ℕ) (hr : r ≤ N)
    (S : PlacementSubset r (N-r))
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) :
    setPlacement N r hr (castSlotSet (Nat.add_sub_of_le hr) S.val) A =
      rawSubsetPlacement N r hr S A := by
  classical
  have hc : (castSlotSet (Nat.add_sub_of_le hr) S.val).card=r := by
    simpa only [castSlotSet,Finset.card_map] using S.property
  rw [setPlacement,dite_eq_left hc]
  congr 1
  apply Subtype.ext
  change (castSlotSet (Nat.add_sub_of_le hr) S.val).map
    (finCongr (Nat.add_sub_of_le hr).symm).toEmbedding = S.val
  rw [castSlotSet_eq_map,Finset.map_map]
  have he : (finCongr (Nat.add_sub_of_le hr)).toEmbedding.trans
      (finCongr (Nat.add_sub_of_le hr).symm).toEmbedding = Function.Embedding.refl _ := by
    apply Function.Embedding.ext
    intro i
    apply Fin.ext
    rfl
  rw [he,Finset.map_refl]

/-- The literal original overlap fiber and the hypergeometric subset fiber
have exactly the same summands under their canonical coordinate map. -/
theorem sum_overlap_subsets (N k r ell : ℕ) (hk : k ≤ N) (hr : r ≤ N)
    {M : Type*} [AddCommMonoid M] (F : Finset (Fin N) → M) :
    (∑ S ∈ (Finset.univ : Finset (PlacementSubset r (N-r))).filter
      (fun S => overlap N k r hk hr S=ell),
      F (castSlotSet (Nat.add_sub_of_le hr) S.val)) =
    ∑ Q ∈ overlapFiber
      (castSlotSet (Nat.add_sub_of_le hk) (firstPositions (p := k) (q := N-k))) r ell,
      F Q := by
  classical
  refine Finset.sum_bij (fun S _ => castSlotSet (Nat.add_sub_of_le hr) S.val) ?_ ?_ ?_ ?_
  · intro S hS
    obtain ⟨_,he⟩ := Finset.mem_filter.mp hS
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _,by simpa only [castSlotSet,Finset.card_map] using S.property⟩,?_⟩
    simpa only [overlap,castSlotSet_eq_map,Finset.inter_comm] using he
  · intro S _ T _ he
    apply Subtype.ext
    exact Finset.map_injective _ he
  · intro Q hQ
    obtain ⟨hcard,he⟩ := Finset.mem_filter.mp hQ
    have hc := (Finset.mem_powersetCard.mp hcard).2
    refine ⟨sourcePlacementOfSlots hr Q hc,?_,slots_sourcePlacementOfSlots hr Q hc⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    change ((sourcePlacementOfSlots hr Q hc).val.map
      (finCongr (Nat.add_sub_of_le hr)).toEmbedding ∩ _).card=ell
    rw [← castSlotSet_eq_map,slots_sourcePlacementOfSlots]
    simpa only [castSlotSet_eq_map,Finset.inter_comm] using he
  · intro _ _
    rfl

/-- Exact number of actual source placements at each overlap, before any
invariance or operator reduction is used. -/
theorem card_overlap_subsets (N k r ell : ℕ) (hk : k ≤ N) (hr : r ≤ N)
    (hell : ell ≤ r) :
    ((Finset.univ : Finset (PlacementSubset r (N-r))).filter
      (fun S => overlap N k r hk hr S=ell)).card =
      k.choose ell*(N-k).choose (r-ell) := by
  classical
  have he := sum_overlap_subsets N k r ell hk hr (fun _ => (1 : ℕ))
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at he
  rw [he]
  exact card_overlapFiber _ (by simp [castSlotSet,card_firstPositions]) hell

/-- The two independent blocks of a decomposition are uniquely determined
by their union. This injectivity is on the literal subset indices. -/
theorem union_injective_on_decompositions {N r ell : ℕ} (P : Finset (Fin N)) :
    Set.InjOn (fun UV : Finset (Fin N) × Finset (Fin N) => UV.1 ∪ UV.2)
      (overlapDecompositions P r ell) := by
  classical
  have recover (U V : Finset (Fin N)) (hu : U ⊆ P) (hv : V ⊆ Finset.univ \ P) :
      (U ∪ V) ∩ P = U ∧ (U ∪ V) \ P = V := by
    constructor <;> ext x <;> by_cases hx : x ∈ P
    · simp only [Finset.mem_inter,Finset.mem_union,hx,and_true]
      exact or_iff_left (fun h => (Finset.mem_sdiff.mp (hv h)).2 hx)
    · simp only [Finset.mem_inter,Finset.mem_union,hx,and_false,false_iff]
      exact fun h => hx (hu h)
    · simp only [Finset.mem_sdiff,hx,not_true_eq_false,and_false,false_iff]
      exact fun h => (Finset.mem_sdiff.mp (hv h)).2 hx
    · simp only [Finset.mem_sdiff,Finset.mem_union,hx,not_false_eq_true,and_true]
      exact or_iff_right (fun h => hx (hu h))
  intro a ha b hb hab
  obtain ⟨haU,haV⟩ := Finset.mem_product.mp ha
  obtain ⟨hbU,hbV⟩ := Finset.mem_product.mp hb
  have ar := recover a.1 a.2 (Finset.mem_powersetCard.mp haU).1
    (Finset.mem_powersetCard.mp haV).1
  have br := recover b.1 b.2 (Finset.mem_powersetCard.mp hbU).1
    (Finset.mem_powersetCard.mp hbV).1
  exact Prod.ext
    (ar.1.symm.trans ((congrArg (fun Q => Q ∩ P) hab).trans br.1))
    (ar.2.symm.trans ((congrArg (fun Q => Q \ P) hab).trans br.2))

/-- Exact sum over a fixed overlap is the sum over observed subsets and
spectator subsets, retaining the full operator-valued dependence. -/
theorem sum_overlap_decompositions {N r ell : ℕ} (P : Finset (Fin N))
    (hell : ell ≤ r) {M : Type*} [AddCommMonoid M]
    (F : Finset (Fin N) → M) :
    (∑ Q ∈ overlapFiber P r ell, F Q) =
      ∑ U ∈ P.powersetCard ell, ∑ V ∈ (Finset.univ \ P).powersetCard (r-ell), F (U ∪ V) := by
  classical
  rw [overlapFiber_eq_decomposition_image P hell,
    Finset.sum_image (union_injective_on_decompositions P)]
  exact Finset.sum_product _ _ _

/-- The exact multiplicity for each fixed observed subset. -/
theorem spectator_choices {N k r ell : ℕ} (P : Finset (Fin N)) (hP : P.card=k) :
    ((Finset.univ \ P).powersetCard (r-ell)).card=(N-k).choose (r-ell) := by
  rw [Finset.card_powersetCard,Finset.card_sdiff_of_subset (Finset.subset_univ P)]
  simp only [Finset.card_univ,Fintype.card_fin,hP]

/-- Every operator in the frozen overlap partition is now indexed by the
literal observed and spectator subsets, with no supplied reduction hypothesis. -/
theorem overlap_trace_decomposition (k m r ell : ℕ) (hr : r ≤ k+m) (hell : ell ≤ r)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (T : RankOperator H (k+m)) (hT : IsTraceClass T) :
    (splitMap k m (overlapIdeal (k+m) k r ell (by omega) hr A ⟨T,hT⟩)).val =
      ∑ U ∈ (castSlotSet (Nat.add_sub_of_le (show k ≤ k+m by omega))
        (firstPositions (p := k) (q := k+m-k))).powersetCard ell,
      ∑ V ∈ (Finset.univ \ castSlotSet (Nat.add_sub_of_le (show k ≤ k+m by omega))
        (firstPositions (p := k) (q := k+m-k))).powersetCard (r-ell),
        splitTrace k m (setPlacement (k+m) r hr (U ∪ V) A*T-
          T*setPlacement (k+m) r hr (U ∪ V) A) (commutator_finite _ T hT) := by
  classical
  calc
    _ = ∑ S ∈ (Finset.univ : Finset (PlacementSubset r (k+m-r))).filter
        (fun S => overlap (k+m) k r (by omega) hr S=ell),
        splitTrace k m (rawSubsetPlacement (k+m) r hr S A*T-
          T*rawSubsetPlacement (k+m) r hr S A) (commutator_finite _ T hT) := by
      simp only [overlapIdeal,map_sum,Submodule.coe_sum,splitMap_val,commutatorIdeal]
    _ = ∑ Q ∈ overlapFiber
        (castSlotSet (Nat.add_sub_of_le (show k ≤ k+m by omega))
          (firstPositions (p := k) (q := k+m-k))) r ell,
        splitTrace k m (setPlacement (k+m) r hr Q A*T-T*setPlacement (k+m) r hr Q A)
          (commutator_finite _ T hT) := by
      simpa only [setPlacement_slots] using sum_overlap_subsets (k+m) k r ell (by omega) hr
        (fun Q => splitTrace k m
          (setPlacement (k+m) r hr Q A*T-T*setPlacement (k+m) r hr Q A)
            (commutator_finite _ T hT))
    _ = _ := sum_overlap_decompositions _ hell _

end QuantumNLS.Prop001RsixteenCounting

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RsixteenCounting" then
      pending := pending.push n
      roots := roots + 1
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
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop001RsixteenCounting audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."



#print axioms QuantumNLS.Prop001RsixteenCounting.castSlotSet_eq_map
#print axioms QuantumNLS.Prop001RsixteenCounting.setPlacement_slots
#print axioms QuantumNLS.Prop001RsixteenCounting.sum_overlap_subsets
#print axioms QuantumNLS.Prop001RsixteenCounting.card_overlap_subsets
#print axioms QuantumNLS.Prop001RsixteenCounting.union_injective_on_decompositions
#print axioms QuantumNLS.Prop001RsixteenCounting.sum_overlap_decompositions
#print axioms QuantumNLS.Prop001RsixteenCounting.spectator_choices
#print axioms QuantumNLS.Prop001RsixteenCounting.overlap_trace_decomposition

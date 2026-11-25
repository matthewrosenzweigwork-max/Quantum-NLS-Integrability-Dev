import QuantumNLS.Prop001RsixteenCounting

/-! Exact identification of the literal higher-overlap placement remainder. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RsixteenHigher
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementFusion PlacementGrouping
  PlacementOverlap PlacementUnionReindex PlacementFiberTransport PhysicalEnergyTrace
  RootOverlapCommutator Ext025A12Trace Ext025A12Normal Ext025A12PartialTrace Ext025A12Collision
  Prop001 Prop001RfourteenRegrouping Prop001RfourteenTraceRegrouping
  Prop001RfifteenTransport Prop001RfifteenRemainder Prop001RsixteenCounting
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The arithmetic packaging of the observed set keeps its literal slots. -/
theorem observedSlots_eq (k m : ℕ) :
    castSlotSet (Nat.add_sub_of_le (show k ≤ k+m by omega))
      (firstPositions (p := k) (q := k+m-k)) = firstPositions (p := k) (q := m) := by
  unfold castSlotSet firstPositions
  rw [Finset.map_map]
  apply congrArg (fun e : Fin k ↪ Fin (k+m) => Finset.univ.map e)
  apply Function.Embedding.ext
  intro i
  apply Fin.ext
  change (Equiv.cast (congrArg Fin (Nat.add_sub_of_le (show k ≤ k+m by omega)))
    (Fin.castAdd (k+m-k) i)).val = (Fin.castAdd m i).val
  rw [equivCast_eq_finCast (Nat.add_sub_of_le (show k ≤ k+m by omega))
    (Fin.castAdd (k+m-k) i)]; rfl

/-- Exact operator-valued disintegration of the two-overlap event. -/
theorem sum_multiple_overlap {N : ℕ} (P : Finset (Fin N)) (r : ℕ)
    {M : Type*} [AddCommMonoid M] (F : Finset (Fin N) → M) :
    (∑ Q ∈ multipleOverlapEvent P r,F Q) =
      ∑ s ∈ Finset.range (r-1),∑ Q ∈ overlapFiber P r (s+2),F Q := by
  classical
  have hmap : (↑(multipleOverlapEvent P r) : Set (Finset (Fin N))).MapsTo
      (fun Q => (P ∩ Q).card-2) (Finset.range (r-1)) := by
    intro Q hQ
    obtain ⟨hQr,h2⟩ := Finset.mem_filter.mp hQ
    have hcard := (Finset.mem_powersetCard.mp hQr).2
    have hle := Finset.card_le_card (Finset.inter_subset_right : P ∩ Q ⊆ Q)
    apply Finset.mem_range.mpr
    change (P ∩ Q).card-2 < r-1
    omega
  calc
    _ = ∑ s ∈ Finset.range (r-1),
        ∑ Q ∈ (multipleOverlapEvent P r).filter (fun Q => (P ∩ Q).card-2=s),F Q :=
      (Finset.sum_fiberwise_of_maps_to hmap F).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      have hf : ((multipleOverlapEvent P r).filter (fun Q => (P ∩ Q).card-2=s)) =
          overlapFiber P r (s+2) := by
        ext Q
        simp only [multipleOverlapEvent,overlapFiber,Finset.mem_filter]
        constructor
        · rintro ⟨⟨hQ,h2⟩,he⟩
          exact ⟨hQ,by omega⟩
        · rintro ⟨hQ,he⟩
          exact ⟨⟨hQ,by omega⟩,by omega⟩
      rw [hf]

/-- Every traced overlapIdeal is the corresponding sum of literal
setPlacement commutators, including impossible and zero overlap fibers. -/
theorem traced_overlap_literal (k m r ell : ℕ) (hr : r ≤ k+m)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (T : RankOperator H (k+m)) (hT : IsTraceClass T) :
    (splitMap k m (overlapIdeal (k+m) k r ell (by omega) hr A ⟨T,hT⟩)).val =
      ∑ Q ∈ overlapFiber (firstPositions (p := k) (q := m)) r ell,
        splitTrace k m (setPlacement (k+m) r hr Q A*T-T*setPlacement (k+m) r hr Q A)
          (commutator_finite _ T hT) := by
  classical
  calc
    _ = ∑ S ∈ (Finset.univ : Finset (PlacementSubset r (k+m-r))).filter
        (fun S => overlap (k+m) k r (by omega) hr S=ell),
        splitTrace k m (rawSubsetPlacement (k+m) r hr S A*T-
          T*rawSubsetPlacement (k+m) r hr S A) (commutator_finite _ T hT) := by
      simp only [overlapIdeal,map_sum,Submodule.coe_sum,splitMap_val,commutatorIdeal]
    _ = _ := by
      simpa only [setPlacement_slots,observedSlots_eq] using
        sum_overlap_subsets (k+m) k r ell (by omega) hr
          (fun Q => splitTrace k m
            (setPlacement (k+m) r hr Q A*T-T*setPlacement (k+m) r hr Q A)
              (commutator_finite _ T hT))

/-- The concrete multipleRank candidate is exactly the weighted sum of
all original traced overlap fibers with ell>=2. -/
theorem higher_overlap_eq_multipleRank (k m n : ℕ) (hr : n+1 ≤ k+m)
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1))
    (T : RankOperator H (k+m)) (hT : IsTraceClass T) :
    (((((n+1).factorial : ℝ)*(k+m)/(k+m : ℝ)^(n+1)) : ℝ) : ℂ) •
      (∑ s ∈ Finset.range n,
        (splitMap k m (overlapIdeal (k+m) k (n+1) (s+2) (by omega) hr A ⟨T,hT⟩)).val) =
      multipleRank k m (n+1) hr (firstPositions (p := k) (q := m)) A T hT := by
  classical
  unfold multipleRank
  congr 1
  simp_rw [traced_overlap_literal]
  exact (by simpa only [Nat.add_sub_cancel] using
    (sum_multiple_overlap (firstPositions (p := k) (q := m)) (n+1)
      (fun Q => splitTrace k m
        (setPlacement (k+m) (n+1) hr Q A*T-T*setPlacement (k+m) (n+1) hr Q A)
          (commutator_finite _ T hT))).symm)

/-- Exact identification at all interaction ranks, using the original
factorial source weights and original multi-overlap placement sums. -/
theorem higher_overlap_eq_multipleRemainder (D : ClassicalData H) (k m : ℕ)
    (T : RankOperator H (k+m)) (hT : IsTraceClass T) :
    (∑ n : Fin (k+m),
      (((((n.val+1).factorial : ℝ)*(k+m)/(k+m : ℝ)^(n.val+1)) : ℝ) : ℂ) •
        (∑ s ∈ Finset.range n.val,
          (splitMap k m (overlapIdeal (k+m) k (n.val+1) (s+2) (by omega)
            (Nat.succ_le_of_lt n.isLt) (D.A n.val) ⟨T,hT⟩)).val)) =
      multipleRemainder D k m (firstPositions (p := k) (q := m)) T hT := by
  classical
  unfold multipleRemainder
  exact Finset.sum_congr rfl (fun n _ =>
    higher_overlap_eq_multipleRank k m n.val (Nat.succ_le_of_lt n.isLt) (D.A n.val) T hT)

end QuantumNLS.Prop001RsixteenHigher

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RsixteenHigher" then
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
  Lean.logInfo m!"Prop001RsixteenHigher audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."



#print axioms QuantumNLS.Prop001RsixteenHigher.observedSlots_eq
#print axioms QuantumNLS.Prop001RsixteenHigher.sum_multiple_overlap
#print axioms QuantumNLS.Prop001RsixteenHigher.traced_overlap_literal
#print axioms QuantumNLS.Prop001RsixteenHigher.higher_overlap_eq_multipleRank
#print axioms QuantumNLS.Prop001RsixteenHigher.higher_overlap_eq_multipleRemainder

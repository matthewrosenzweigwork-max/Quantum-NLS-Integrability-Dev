import QuantumNLS.Prop001RfifteenFinite

/-! Canonical placement support for the actual finite-marginal reduction.
The prefix lifting proofs are adapted from the frozen LOCAL-011 dense-tensor
transport; no frozen declaration or file is changed. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Prop001RsixteenPlacement
open TraceClass TraceIdeal TensorCarrier TensorPlacements PlacementFusion PlacementGrouping
  PhysicalTensor PhysicalEnergyTrace RootOverlapCommutator PlacementFiberOperator
  Ext025A12Trace Ext025A12Normal Ext025A12PartialTrace Ext025A12Collision
  Prop001 Prop001RfifteenTransport Prop001RfifteenNestedTrace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- The product-vector formula for applying the first-block placement. -/
omit [CompleteSpace H] in
theorem firstPlacement_ptC {p q : ℕ}
    (A : SymSector ℂ H p →L[ℂ] SymSector ℂ H p)
    (a : Fin p → H) (b : Fin q → H) :
    firstPlacement (q := q) A (ptC (Fin.append a b)) =
      (splitIsometry p q).symm
        (htmul (extendSymKernel A (ptC a)) (ptC b)) := by
  unfold firstPlacement
  simp only [ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [splitIsometry_ptprod_append, htmap_htmul, ContinuousLinearMap.id_apply]

/-- Prefix-lifting the first-block placement is the first-block placement
after the three tensor blocks have been reassociated. -/
theorem prefixTensorLift_firstPlacement {k m t : ℕ}
    (A : SymSector ℂ H k →L[ℂ] SymSector ℂ H k) :
    castTensorOperator (Nat.add_assoc k m t)
      (prefixTensorLift (H := H) (r := k + m) (t := t)
        (firstPlacement (q := m) A)) = firstPlacement (q := m + t) A := by
  apply eq_of_eq_on_ptC
  intro f
  let a : Fin k → H := fun i => f (Fin.castAdd (m + t) i)
  let b : Fin m → H := fun i => f (Fin.natAdd k (Fin.castAdd t i))
  let c : Fin t → H := fun i => f (Fin.natAdd k (Fin.natAdd m i))
  have hf : f = Fin.append a (Fin.append b c) := by
    exact eq_append3 f
  rw [hf, castTensorOperator_eq_conj, cIso_symm_ptC]
  have hcast :
      (fun i : Fin ((k + m) + t) =>
        (Fin.append a (Fin.append b c)) (Fin.cast (Nat.add_assoc k m t) i)) =
        Fin.append (Fin.append a b) c := by
    funext i
    refine Fin.addCases (fun j : Fin (k + m) => ?_) (fun j : Fin t => ?_) i
    · refine Fin.addCases (fun j : Fin k => ?_) (fun j : Fin m => ?_) j
      · have hi : Fin.cast (Nat.add_assoc k m t) (Fin.castAdd t (Fin.castAdd m j)) =
            Fin.castAdd (m + t) j := by
          apply Fin.ext
          simp
        rw [hi]
        simp [Fin.append]
      · have hi : Fin.cast (Nat.add_assoc k m t)
              (Fin.castAdd t (Fin.natAdd k j)) = Fin.natAdd k (Fin.castAdd t j) := by
          apply Fin.ext
          simp
        rw [hi]
        simp [Fin.append]
    · have hi : Fin.cast (Nat.add_assoc k m t) (Fin.natAdd (k + m) j) =
          Fin.natAdd k (Fin.natAdd m j) := by
        apply Fin.ext
        simp
        omega
      rw [hi]
      simp [Fin.append]
  rw [show (ptC (fun i : Fin ((k + m) + t) =>
      (Fin.append a (Fin.append b c)) (Fin.cast (Nat.add_assoc k m t) i)) :
      HilbertTensorPower ℂ H ((k + m) + t)) = ptC (Fin.append (Fin.append a b) c) by
        rw [hcast]]
  unfold prefixTensorLift
  simp only [ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [splitIsometry_ptprod_append, htmap_htmul, ContinuousLinearMap.id_apply,
    firstPlacement_ptC, firstPlacement_ptC]
  exact split_assoc_ptC (extendSymKernel A (ptC a)) b c

/-- The subset placement induced on a longer prefix by a local placement. -/
def prefixPlacementSubset {k m t : ℕ}
    (S : PlacementSubset k m) : PlacementSubset k (m + t) := by
  refine ⟨S.1.map (Fin.castLEEmb (by omega)), ?_⟩
  rw [Finset.card_map]
  exact S.2

omit [CompleteSpace H] in
theorem castTensorOperator_comp {m n : ℕ} (h : m = n)
    (X Y : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) :
    castTensorOperator h (X.comp Y) =
      (castTensorOperator h X).comp (castTensorOperator h Y) := by
  cases h
  rfl

omit [CompleteSpace H] in
theorem castTensorOperator_permRep {m n : ℕ} (h : m = n)
    (σ : Equiv.Perm (Fin m)) :
    castTensorOperator h (permRep ℂ H m σ :
      HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m) =
      (permRep ℂ H n (castPermBack h.symm σ) :
        HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) := by
  cases h
  rfl

theorem castPermBack_apply {m n : ℕ} (h : m = n)
    (σ : Equiv.Perm (Fin n)) (i : Fin m) :
    castPermBack h σ i = Fin.cast h.symm (σ (Fin.cast h i)) := by
  cases h
  rfl

omit [CompleteSpace H] in
theorem permRep_inv_clm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permRep ℂ H n σ⁻¹ :
      HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) =
      (↑((permRep ℂ H n σ)⁻¹) :
        HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) := by
  exact congrArg (fun U : unitary
      (HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) =>
        (U : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n))
    (map_inv (permRep ℂ H n) σ)

theorem castBlockPerm_prefix {k m t : ℕ}
    (h : (k + m) + t = k + (m + t))
    (τ : Equiv.Perm (Fin (k + m))) (i : Fin k) :
    castPermBack h.symm (blockPerm τ (1 : Equiv.Perm (Fin t)))
        (Fin.castAdd (m + t) i) =
      Fin.castLE (by omega) (τ (Fin.castAdd m i)) := by
  have hcast :
      Fin.cast h.symm (Fin.castAdd (m + t) i) =
        Fin.castAdd t (Fin.castAdd m i) := by
    apply Fin.ext
    simp
  have hback (j : Fin (k + m)) :
      Fin.cast h (Fin.castAdd t j) = Fin.castLE (by omega) j := by
    apply Fin.ext
    simp
  rw [castPermBack_apply]
  rw [hcast, blockPerm_castAdd]
  exact hback _

def conjugateTensorOperator {n : ℕ} (σ : Equiv.Perm (Fin n))
    (T : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) :
    HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n :=
  ((permRep ℂ H n σ : HilbertTensorPower ℂ H n →L[ℂ]
      HilbertTensorPower ℂ H n).comp T).comp
    (permRep ℂ H n σ⁻¹ : HilbertTensorPower ℂ H n →L[ℂ]
      HilbertTensorPower ℂ H n)

/- The proof only needs the Hilbert tensor structure, not completeness. -/
omit [CompleteSpace H] in
theorem prefixTensorLift_permutedPlacement {k m t : ℕ}
    (τ : Equiv.Perm (Fin (k + m)))
    (A : SymSector ℂ H k →L[ℂ] SymSector ℂ H k) :
    prefixTensorLift (H := H) (r := k + m) (t := t)
        (permutedPlacement τ A) =
      conjugateTensorOperator (blockPerm τ (1 : Equiv.Perm (Fin t)))
        (prefixTensorLift (H := H) (r := k + m) (t := t)
          (firstPlacement (q := m) A)) := by
  unfold permutedPlacement conjugateTensorOperator
  rw [← prefixTensorLift_comp, ← prefixTensorLift_comp]
  rw [prefixTensorLift_permRep, prefixTensorLift_permRep]
  have hinv : blockPerm τ⁻¹ (1 : Equiv.Perm (Fin t)) =
      (blockPerm τ (1 : Equiv.Perm (Fin t)))⁻¹ := by
    exact (blockPerm_symm τ (1 : Equiv.Perm (Fin t))).symm
  rw [hinv]

/-- Prefix lifting a local subset placement gives the corresponding placement
on the longer tensor power, with the same ordered kernel action. -/
theorem prefixTensorLift_subsetPlacement {k m t : ℕ}
    (S : PlacementSubset k m)
    (A : SymSector ℂ H k →L[ℂ] SymSector ℂ H k) :
    castTensorOperator (Nat.add_assoc k m t)
      (prefixTensorLift (H := H) (r := k + m) (t := t)
        (subsetPlacement S A)) =
      subsetPlacement (prefixPlacementSubset (t := t) S) A := by
  let τ := subsetRepresentative S
  have hrep : placementSubsetOfPerm τ = S := subsetRepresentative_maps S
  have hlocal : subsetPlacement S A = permutedPlacement τ A :=
    (permutedPlacement_eq_subsetPlacement τ S hrep A).symm
  let ρ := blockPerm τ (1 : Equiv.Perm (Fin t))
  let σ := castPermBack (Nat.add_assoc k m t).symm ρ
  rw [hlocal, prefixTensorLift_permutedPlacement]
  have hbase := prefixTensorLift_firstPlacement (H := H) (k := k) (m := m) (t := t) A
  calc
    castTensorOperator (Nat.add_assoc k m t)
        (conjugateTensorOperator ρ
          (prefixTensorLift (H := H) (r := k + m) (t := t)
            (firstPlacement (q := m) A))) =
      permutedPlacement σ A := by
      unfold conjugateTensorOperator
      rw [castTensorOperator_comp, castTensorOperator_comp,
        castTensorOperator_permRep, hbase, castTensorOperator_permRep]
      simp [σ, castPermBack_inv]
      unfold permutedPlacement
      rw [permRep_inv_clm]
    _ = subsetPlacement (prefixPlacementSubset (t := t) S) A := by
      have himage : placementSubsetOfPerm σ = prefixPlacementSubset (t := t) S := by
        apply Subtype.ext
        change (firstPositions (p := k) (q := m + t)).map σ.toEmbedding =
          S.1.map (Fin.castLEEmb (show k + m ≤ k + (m + t) by omega))
        have hrepSet : S.1 =
            (firstPositions (p := k) (q := m)).map τ.toEmbedding := by
          exact (congrArg Subtype.val hrep).symm
        rw [hrepSet]
        unfold firstPositions
        rw [Finset.map_map, Finset.map_map]
        ext x
        simp only [Finset.mem_map, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, rfl⟩
          refine ⟨Fin.castAdd m i, ⟨i, rfl⟩, ?_⟩
          calc
            ((τ.toEmbedding).trans
                (Fin.castLEEmb (show k + m ≤ k + (m + t) by omega)))
                (Fin.castAdd m i) = Fin.castLE (by omega)
                  (τ (Fin.castAdd m i)) := rfl
            _ = σ (Fin.castAdd (m + t) i) :=
              (castBlockPerm_prefix (Nat.add_assoc k m t) τ i).symm
        · rintro ⟨i, hi, hix⟩
          obtain ⟨j, hji⟩ := hi
          subst i
          refine ⟨j, ?_⟩
          change σ (Fin.castAdd (m + t) j) = x
          calc
            σ (Fin.castAdd (m + t) j) = Fin.castLE (by omega)
                (τ (Fin.castAdd m j)) :=
              castBlockPerm_prefix (Nat.add_assoc k m t) τ j
            _ = ((τ.toEmbedding).trans
                (Fin.castLEEmb (show k + m ≤ k + (m + t) by omega)))
                (Fin.castAdd m j) := rfl
            _ = x := hix
      exact permutedPlacement_eq_subsetPlacement σ _ himage A


/-- The two prefix-lift implementations are the same bounded operator. -/
theorem prefixTensorLift_eq (k m : ℕ) (B : RankOperator H k) :
    prefixTensorLift (t := m) B = prefixLift k m B := rfl

/-- The actual canonical subset on a longer tensor power acts only on the
prefix marginal. This identifies operators, not just their norms. -/
theorem prefix_subset_commutator_reduction (r s t k m : ℕ) (h : r+s=k+m)
    (S : PlacementSubset r s)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (T : RankOperator H ((k+m)+t)) (hT : IsTraceClass T) :
    let B := castTensorOperator h (subsetPlacement S A)
    splitTrace k (m+t) (pull (cIso (Nat.add_assoc k m t)).symm
      (prefixLift (k+m) t B*T-T*prefixLift (k+m) t B))
      (by simpa only [IsTraceClass,traceNorm_pull] using commutator_finite _ T hT) =
    splitTrace k m (B*splitTrace (k+m) t T hT-splitTrace (k+m) t T hT*B)
      (commutator_finite _ _ (splitTrace_finite (k+m) t T hT)) :=
  nested_commutator_reduction k m t _ T hT

/-- Canonical placed commutators reduce to actual pure-state marginals.
There is no unknown operator, marginal equation, or rate in the premises. -/
theorem canonical_subset_pure_reduction (r s t k m : ℕ) (h : r+s=k+m)
    (S : PlacementSubset r s)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r)
    (z : HilbertTensorPower ℂ H ((k+m)+t)) :
    let B := castTensorOperator h (subsetPlacement S A)
    let P := InnerProductSpace.rankOne ℂ z z
    splitTrace k (m+t) (pull (cIso (Nat.add_assoc k m t)).symm
      (prefixLift (k+m) t B*P-P*prefixLift (k+m) t B))
      (by simpa only [IsTraceClass,traceNorm_pull] using commutator_finite _ P (rankOne_finite z z)) =
    splitTrace k m (B*reducedDensityN ((k+m)+t) (k+m) (by omega) z-
      reducedDensityN ((k+m)+t) (k+m) (by omega) z*B)
      (commutator_finite _ _ (reducedDensity_finite _ _ (by omega) z)) := by
  dsimp only
  simpa only [splitTrace_rankOne] using
    prefix_subset_commutator_reduction r s t k m h S A
      (InnerProductSpace.rankOne ℂ z z) (rankOne_finite z z)

/-- Prefix extension is the original literal raw placement for its displayed
subset, including the arithmetic carrier transport. -/
theorem raw_prefix_placement (r s t : ℕ)
    (S : PlacementSubset r s)
    (A : SymSector ℂ H r →L[ℂ] SymSector ℂ H r) :
    castTensorOperator (Nat.add_assoc r s t)
      (prefixLift (r+s) t (subsetPlacement S A)) =
      subsetPlacement (prefixPlacementSubset (t := t) S) A := by
  rw [← prefixTensorLift_eq]
  exact prefixTensorLift_subsetPlacement S A

end QuantumNLS.Prop001RsixteenPlacement
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RsixteenPlacement" then
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
  Lean.logInfo m!"Prop001RsixteenPlacement audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."


#print axioms QuantumNLS.Prop001RsixteenPlacement.firstPlacement_ptC
#print axioms QuantumNLS.Prop001RsixteenPlacement.prefixTensorLift_firstPlacement
#print axioms QuantumNLS.Prop001RsixteenPlacement.prefixPlacementSubset
#print axioms QuantumNLS.Prop001RsixteenPlacement.castTensorOperator_comp
#print axioms QuantumNLS.Prop001RsixteenPlacement.castTensorOperator_permRep
#print axioms QuantumNLS.Prop001RsixteenPlacement.castPermBack_apply
#print axioms QuantumNLS.Prop001RsixteenPlacement.permRep_inv_clm
#print axioms QuantumNLS.Prop001RsixteenPlacement.castBlockPerm_prefix
#print axioms QuantumNLS.Prop001RsixteenPlacement.conjugateTensorOperator
#print axioms QuantumNLS.Prop001RsixteenPlacement.prefixTensorLift_permutedPlacement
#print axioms QuantumNLS.Prop001RsixteenPlacement.prefixTensorLift_subsetPlacement
#print axioms QuantumNLS.Prop001RsixteenPlacement.prefixTensorLift_eq
#print axioms QuantumNLS.Prop001RsixteenPlacement.prefix_subset_commutator_reduction
#print axioms QuantumNLS.Prop001RsixteenPlacement.canonical_subset_pure_reduction
#print axioms QuantumNLS.Prop001RsixteenPlacement.raw_prefix_placement

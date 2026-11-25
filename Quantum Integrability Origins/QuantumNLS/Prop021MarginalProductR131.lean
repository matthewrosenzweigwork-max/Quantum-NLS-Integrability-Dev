import QuantumNLS.Prop021SlotUnionR130

/-! The ordered condensate projections give the partial tensor projector
in the actual reduced density, for every positive rank. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 20000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop021MarginalProductR131
open TensorCarrier TensorFourier PhysicalTensor TraceClass Prop021SlotUnionR130
open Prop021ProjectionUnionR128 Prop021ExcitationR130
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "Tensor" => HilbertTensorPower ℂ H

private def pure {n : ℕ} (f : Fin n → H) : Tensor n :=
  ((ptprod f : AlgTensorPower ℂ H n) : Tensor n)

private def select {n : ℕ} (u : H) (S : Finset (Fin n)) (f : Fin n → H) : Fin n → H :=
  fun i => if i ∈ S then ⟪u, f i⟫_ℂ • u else f i

private lemma split_pure (k r : ℕ) (f : Fin (k+r) → H) :
    splitIsometry k r (pure f) =
      htmul (pure fun i => f (Fin.castAdd r i)) (pure fun i => f (Fin.natAdd k i)) := by
  let a : Fin k → H := fun i => f (Fin.castAdd r i)
  let b : Fin r → H := fun i => f (Fin.natAdd k i)
  have h : Fin.append a b = f := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [a, b]
  simpa only [pure, h] using splitIsometry_ptprod_append (𝕜 := ℂ) a b

private lemma rankOne_pure (k : ℕ) (u : H) (f : Fin k → H) :
    InnerProductSpace.rankOne ℂ (htpow k u : Tensor k) (htpow k u) (pure f) =
      pure (fun i => ⟪u, f i⟫_ℂ • u) := by
  have hinner : ⟪(htpow k u : Tensor k), pure f⟫_ℂ = ∏ i, ⟪u, f i⟫_ℂ := by
    exact (UniformSpace.Completion.inner_coe _ _).trans (inner_ptprod _ _)
  rw [InnerProductSpace.rankOne_apply, hinner]
  change ((∏ i, ⟪u, f i⟫_ℂ) • (pure fun _ : Fin k => u)) = _
  unfold pure
  rw [← UniformSpace.Completion.coe_smul]
  have he : (∏ i, ⟪u, f i⟫_ℂ) • (ptprod (fun _ : Fin k => u) : AlgTensorPower ℂ H k) =
      ptprod (fun i => ⟪u, f i⟫_ℂ • u) :=
    ((PiTensorProduct.tprod ℂ).map_smul_univ (fun i => ⟪u, f i⟫_ℂ) (fun _ => u)).symm
  exact congrArg (fun x : AlgTensorPower ℂ H k => (x : Tensor k)) he

private lemma block_pure (k r : ℕ) (u : H) (f : Fin (k+r) → H) :
    blockPlacement k r (InnerProductSpace.rankOne ℂ (htpow k u : Tensor k) (htpow k u))
      (pure f) =
    pure (select u (Finset.univ.map (Fin.castAddEmb r)) f) := by
  classical
  apply (splitIsometry (𝕜 := ℂ) (E := H) k r).injective
  rw [split_blockPlacement, split_pure, htmap_htmul, ContinuousLinearMap.id_apply,
    rankOne_pure, split_pure]
  congr 1
  · apply congrArg pure
    funext i
    simp [select]
  · apply congrArg pure
    funext i
    have hi : Fin.natAdd k i ∉ (Finset.univ : Finset (Fin k)).map (Fin.castAddEmb r) := by
      rw [Finset.mem_map]
      rintro ⟨j, _, hj⟩
      have he := congrArg Fin.val hj
      change j.val = k+i.val at he
      omega
    simp [select, hi]

private lemma perm_pure {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Fin n → H) :
    permHilbertIsometry σ (pure f) = pure (fun j => f (σ.symm j)) := by
  rw [pure, permHilbertIsometry_coe, permLinearEquiv_ptprod]
  rfl

private lemma slot_pure (u : H) (m : ℕ) (i : Fin (1+m)) (f : Fin (1+m) → H) :
    slot u m i (pure f) = pure (select u {i} f) := by
  classical
  let σ : Equiv.Perm (Fin (1+m)) := Equiv.swap 0 i
  change permHilbertIsometry σ (firstProjection u m ((permHilbertIsometry σ).symm (pure f))) = _
  have hsymm : (permHilbertIsometry (𝕜 := ℂ) (E := H) σ).symm (pure f) =
      pure (fun j => f (σ j)) := by
    apply (permHilbertIsometry (𝕜 := ℂ) (E := H) σ).injective
    simp only [LinearIsometryEquiv.apply_symm_apply, perm_pure, Equiv.apply_symm_apply]
  have hzero : (Finset.univ : Finset (Fin 1)).map (Fin.castAddEmb m) = {0} := by
    ext j
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      have : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    · rintro rfl
      exact ⟨0, rfl⟩
  rw [hsymm, firstProjection, block_pure, hzero, perm_pure]
  apply congrArg pure
  funext j
  have hj : σ.symm j = 0 ↔ j = i := by
    rw [Equiv.symm_apply_eq]
    simp [σ]
  simp [select, hj]

/-- Ordered application of the literal slot projections as a complex map. -/
private def slots (u : H) (m : ℕ) : List (Fin (1+m)) → Tensor (1+m) →L[ℂ] Tensor (1+m)
  | [] => ContinuousLinearMap.id ℂ _
  | i :: is => (slot u m i).comp (slots u m is)

private lemma slots_eq_projectList (u : H) (hu : ‖u‖ = 1) (m : ℕ)
    (is : List (Fin (1+m))) (x : Tensor (1+m)) :
    slots u m is x =
      projectList (is.map fun i => realProjection (slot u m i) (slot_projection u hu m i)) x := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      change slot u m i (slots u m is x) = slot u m i (projectList _ x)
      rw [ih]

private lemma slots_pure (u : H) (hu : ‖u‖ = 1) (m : ℕ) (is : List (Fin (1+m)))
    (f : Fin (1+m) → H) : slots u m is (pure f) = pure (select u is.toFinset f) := by
  classical
  induction is with
  | nil =>
      change pure f = pure (select u ∅ f)
      apply congrArg (fun g : Fin (1+m) → H => pure g)
      funext i
      simp [select]
  | cons i is ih =>
      change slot u m i (slots u m is (pure f)) = _
      rw [ih, slot_pure]
      apply congrArg pure
      funext j
      by_cases hji : j = i
      · subst j
        by_cases hi : i ∈ is
        · simp [select, hi, hu]
        · simp [select, hi]
      · simp [select, hji]

/-- On a positive sector expressed as 1+m, the ordered product is
the one projection onto the first k factors' condensate tensor. -/
theorem ordered_slots_eq_block (u : H) (hu : ‖u‖ = 1) (m k r : ℕ)
    (h : 1+m = k+r) (x : Tensor (1+m)) :
    castHTP h
        (projectList ((List.ofFn (fun j : Fin k => Fin.cast h.symm (Fin.castAdd r j))).map
          fun i => realProjection (slot u m i) (slot_projection u hu m i)) x) =
      blockPlacement k r (InnerProductSpace.rankOne ℂ (htpow k u : Tensor k) (htpow k u))
        (castHTP h x) := by
  classical
  let is := List.ofFn (fun j : Fin k => Fin.cast h.symm (Fin.castAdd r j))
  let T := blockPlacement k r (InnerProductSpace.rankOne ℂ (htpow k u : Tensor k) (htpow k u))
  let e : Tensor (1+m) ≃ₗᵢ[ℂ] Tensor (k+r) := castHTP h
  change e (projectList (is.map _) x) = T (e x)
  rw [← slots_eq_projectList u hu m is x]
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (e.continuous.comp (slots u m is).continuous) (T.continuous.comp e.continuous)
  | ih z =>
      induction z using AlgTensorPower.induction_on with
      | smul_ptprod c f =>
          simp only [UniformSpace.Completion.coe_smul, map_smul]
          apply congrArg (fun y : Tensor (k+r) => c • y)
          change e (slots u m is (pure f)) = T (e (pure f))
          have cast_pure {n q : ℕ} (hn : n=q) (g : Fin n → H) :
              castHTP hn (pure g) = pure (fun i => g (Fin.cast hn.symm i)) := by
            subst q
            rfl
          rw [slots_pure u hu]
          change castHTP h (pure _) = blockPlacement k r _ (castHTP h (pure f))
          rw [cast_pure, cast_pure, block_pure]
          apply congrArg pure
          funext i
          have hi : Fin.cast h.symm i ∈ is.toFinset ↔
              i ∈ (Finset.univ : Finset (Fin k)).map (Fin.castAddEmb r) := by
            simp only [is, List.mem_toFinset, List.mem_ofFn, Finset.mem_map,
              Finset.mem_univ, true_and]
            constructor
            · rintro ⟨j,hj⟩
              exact ⟨j,Fin.cast_injective h.symm hj⟩
            · rintro ⟨j,hj⟩
              exact ⟨j,congrArg (Fin.cast h.symm) hj⟩
          simp only [select, hi]
      | add z w hz hw => simp only [UniformSpace.Completion.coe_add, map_add, hz, hw]

/-- The defect of the literal first-k projector is the fidelity defect of
the actual reduced density (at unit norm). -/
private lemma density_projection_defect (k r : ℕ) (u : H) (hu : ‖u‖ = 1)
    (x : Tensor (k+r)) (hx : ‖x‖ = 1) :
    1-(⟪(htpow k u : Tensor k),reducedDensityPower k r x (htpow k u)⟫_ℂ).re =
      ‖x-blockPlacement k r (InnerProductSpace.rankOne ℂ
        (htpow k u : Tensor k) (htpow k u)) x‖^2 := by
  let p : Tensor k := htpow (𝕜 := ℂ) k u
  let P : Tensor k →L[ℂ] Tensor k := InnerProductSpace.rankOne ℂ p p
  let e := splitIsometry (𝕜 := ℂ) (E := H) k r
  let R : Tensor (k+r) →L[ℂ] Tensor (k+r) := blockPlacement k r P
  have hp : IsStarProjection P := InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ)
    (by rw [norm_htpow, hu, one_pow] : ‖(htpow k u : Tensor k)‖ = 1)
  have hR : IsStarProjection R := conjugate_projection e.symm _
    (block_projection P hp (F := Tensor r))
  have hd := (realProjection R hR).defect_expectation x
  change ‖x-R x‖^2 = ‖x‖^2-(⟪x,R x⟫_ℂ).re at hd
  have hi := e.inner_map_map x (R x)
  rw [show e (R x) = htmap P (ContinuousLinearMap.id ℂ (Tensor r)) (e x) from
    split_blockPlacement k r P x] at hi
  have hred := inner_reducedDensity_left (𝕜 := ℂ) (e x) (htpow k u) (htpow k u)
  change (⟪reducedDensityPower k r x (htpow k u),(htpow k u : Tensor k)⟫_ℂ) =
    ⟪e x,htmap P (ContinuousLinearMap.id ℂ (Tensor r)) (e x)⟫_ℂ at hred
  have hr : (⟪p,reducedDensityPower k r x p⟫_ℂ).re =
      (⟪reducedDensityPower k r x p,p⟫_ℂ).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  change 1 - (⟪p,reducedDensityPower k r x p⟫_ℂ).re = ‖x-R x‖^2
  rw [hr, hred, hi]
  rw [hx, one_pow] at hd
  exact hd.symm

/-- The source's general k marginal bound in terms of the literal
normalized excitation root. -/
theorem marginal_distance (u : H) (hu : ‖u‖ = 1) (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N)
    (x : SymSector ℂ H N) (hx : ‖x‖ = 1) :
    traceNorm (reducedDensityN N k hk x.val -
      InnerProductSpace.rankOne ℂ (htpow k u : Tensor k) (htpow k u)) ≤
    ENNReal.ofReal (2 * Real.sqrt k * ‖contraction u N x‖) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  let r := 1+m-k
  let h : 1+m = k+r := (Nat.add_sub_cancel' hk).symm
  let e : Tensor (1+m) ≃ₗᵢ[ℂ] Tensor (k+r) := castHTP h
  let is := List.ofFn (fun j : Fin k => Fin.cast h.symm (Fin.castAdd r j))
  let y := projectList (is.map fun i => realProjection (slot u m i) (slot_projection u hu m i)) x.val
  have hnorm : ‖e x.val‖ = 1 := (e.norm_map _).trans hx
  have hunion := physical_slot_union u hu m x is
  change ‖x.val-y‖ ≤ Real.sqrt (is.length : ℝ)*‖contraction u (1+m) x‖ at hunion
  simp only [is, List.length_ofFn] at hunion
  have hdef := density_projection_defect k r u hu (e x.val) hnorm
  change 1 - (⟪(htpow k u : Tensor k),reducedDensityN (1+m) k hk x.val (htpow k u)⟫_ℂ).re =
    ‖e x.val - blockPlacement k r (InnerProductSpace.rankOne ℂ (htpow k u : Tensor k) (htpow k u))
      (e x.val)‖^2 at hdef
  rw [← ordered_slots_eq_block u hu m k r h x.val] at hdef
  change _ = ‖e x.val - e y‖^2 at hdef
  rw [← map_sub, e.norm_map] at hdef
  have hf := Prop021MarginalR128.marginal_fidelity (1+m) k hk x.val hx u hu
  rw [hdef, Real.sqrt_sq (norm_nonneg _)] at hf
  exact hf.trans (ENNReal.ofReal_le_ofReal (by linarith))

end QuantumNLS.Prop021MarginalProductR131

#print axioms QuantumNLS.Prop021MarginalProductR131.ordered_slots_eq_block
#print axioms QuantumNLS.Prop021MarginalProductR131.marginal_distance

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021MarginalProductR131"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R131 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

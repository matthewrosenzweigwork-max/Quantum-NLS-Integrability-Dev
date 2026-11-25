import QuantumNLS.Prop001RfourteenSlots

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace BigOperators
namespace QuantumNLS.Prop001RfourteenContraction
open TraceClass TensorCarrier PhysicalTensor TensorPlacements RootOverlapCommutator PhysicalEnergyTrace
  Ext025A12Collision Prop001RthirteenProduct Ext025A8 Prop001 Prop001RfourteenSlots
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem inner_perm (m : ℕ) (σ : Equiv.Perm (Fin m))
    (x y : HilbertTensorPower ℂ H m) :
    ⟪x,(permRep ℂ H m σ : HilbertTensorPower ℂ H m →L[ℂ] _) y⟫_ℂ =
      ⟪(permRep ℂ H m σ⁻¹ : HilbertTensorPower ℂ H m →L[ℂ] _) x,y⟫_ℂ := by
  conv_lhs => lhs; rw [← permRep_cancel σ⁻¹ x]
  simp only [inv_inv]
  exact (permHilbertIsometry (𝕜 := ℂ) (E := H) σ).inner_map_map _ _

theorem slot_test (k n : ℕ) (j : Fin (k+1)) (f : Fin (k+1) → H) (u : H) :
    (fun i => Fin.append f (fun _ : Fin n => u) (slotEquiv k n j i)) =
      Fin.append (Fin.cons (f j) (fun _ : Fin n => u)) (fun i : Fin k => f (j.succAbove i)) := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) a <;> simp
  · simp

theorem inner_placed_product (k n : ℕ) (j : Fin (k+1))
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1))
    (u : H) (f : Fin (k+1) → H) :
    ⟪(splitIsometry (k+1) n).symm (htmul (ptC f) (htpow n u)),
      placedInteraction k n (subsetRepresentative (oneOverlapSubset k n j)) A
        (htpow ((k+1)+n) u)⟫_ℂ =
      ⟪f j,hartreeContraction (extendSymKernel A) u u⟫_ℂ *
        ∏ i : Fin k, ⟪f (j.succAbove i),u⟫_ℂ := by
  rw [placedInteraction_slotPerm]
  unfold placedInteraction
  rw [castTensorOperator_eq_conj]
  rw [← inner_symm_left]
  change ⟪(cIso (by omega : n+1+k=(k+1)+n)).symm
    ((splitIsometry (k+1) n).symm (htmul (ptC f) (ptC (fun _ : Fin n => u)))),
    permutedPlacement (slotPerm k n j) A
      ((cIso (by omega : n+1+k=(k+1)+n)).symm (htpow ((k+1)+n) u))⟫_ℂ = _
  rw [split_symm_ptC]
  change ⟪(cIso (by omega : n+1+k=(k+1)+n)).symm
      (ptC (Fin.append f (fun _ : Fin n => u))),
    permutedPlacement (slotPerm k n j) A
      ((cIso (by omega : n+1+k=(k+1)+n)).symm (htpow ((k+1)+n) u))⟫_ℂ = _
  rw [cIso_symm_ptC]
  have hpow : (cIso (by omega : n+1+k=(k+1)+n)).symm
      (htpow ((k+1)+n) u : HilbertTensorPower ℂ H ((k+1)+n)) = htpow (n+1+k) u := by
    exact cIso_symm_ptC _ (fun _ => u)
  rw [hpow]
  unfold permutedPlacement
  simp only [ContinuousLinearMap.comp_apply]
  rw [RootOverlapLimit.permRep_htpow,inner_perm,permRep_ptC]
  have ht : (fun i => Fin.append f (fun _ : Fin n => u)
      (Fin.cast (by omega : n+1+k=(k+1)+n) (((slotPerm k n j)⁻¹).symm i))) =
      Fin.append (Fin.cons (f j) (fun _ : Fin n => u)) (fun i : Fin k => f (j.succAbove i)) := by
    simpa [slotPerm,Equiv.Perm.inv_def] using slot_test k n j f u
  rw [ht]
  unfold firstPlacement
  simp only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [inner_symm_right,splitIsometry_ptprod_append,splitIsometry_htpow,
    htmap_htmul,ContinuousLinearMap.id_apply,inner_htmul]
  rw [hartreeContraction_pairing,insertFirst_self]
  congr 1
  exact RootOverlapLimit.inner_ptC_ptC _ (fun _ => u)

/-- Actual one-overlap spectator contraction acting on a coherent tensor. -/
theorem splitContraction_product (k n : ℕ) (j : Fin (k+1))
    (A : SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1)) (u : H) :
    splitContraction (k+1) n
      (placedInteraction k n (subsetRepresentative (oneOverlapSubset k n j)) A) u
      (htpow (k+1) u) =
      tensorMultilinear (k+1) (Function.update (fun _ => u) j
        (hartreeContraction (extendSymKernel A) u u)) := by
  classical
  apply ext_inner_right ℂ
  intro x
  have hx : ∀ f : Fin (k+1) → H,
      ⟪ptC f,splitContraction (k+1) n
        (placedInteraction k n (subsetRepresentative (oneOverlapSubset k n j)) A) u
        (htpow (k+1) u)⟫_ℂ =
      ⟪ptC f,tensorMultilinear (k+1) (Function.update (fun _ => u) j
        (hartreeContraction (extendSymKernel A) u u))⟫_ℂ := by
    intro f
    unfold splitContraction
    erw [Prop001RthirteenProduct.inner_contraction]
    simp only [pull_apply,LinearIsometryEquiv.symm_symm]
    rw [← inner_symm_left,← splitIsometry_htpow,LinearIsometryEquiv.symm_apply_apply,inner_placed_product]
    change _ = ⟪ptC f,ptC (Function.update (fun _ => u) j _)⟫_ℂ
    rw [RootOverlapLimit.inner_ptC_ptC,Fin.prod_univ_succAbove _ j]
    simp only [Function.update_self,Function.update_of_ne (Fin.succAbove_ne _ _)]
  have he := eq_of_eq_on_ptC (innerSL ℂ
      (splitContraction (k+1) n
        (placedInteraction k n (subsetRepresentative (oneOverlapSubset k n j)) A) u
        (htpow (k+1) u)))
    (innerSL ℂ (tensorMultilinear (k+1) (Function.update (fun _ => u) j
      (hartreeContraction (extendSymKernel A) u u)))) (fun f => by
        simp only [innerSL_apply_apply]
        rw [← inner_conj_symm _ (ptC f)]
        conv_rhs => rw [← inner_conj_symm _ (ptC f)]
        exact congrArg (starRingEnd ℂ) (hx f))
  exact congrArg (fun F : HilbertTensorPower ℂ H (k+1) →L[ℂ] ℂ => F x) he

end QuantumNLS.Prop001RfourteenContraction

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop001RfourteenContraction" then
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
  Lean.logInfo m!"Prop001RfourteenContraction audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."


#print axioms QuantumNLS.Prop001RfourteenContraction.inner_perm

#print axioms QuantumNLS.Prop001RfourteenContraction.slot_test

#print axioms QuantumNLS.Prop001RfourteenContraction.inner_placed_product

#print axioms QuantumNLS.Prop001RfourteenContraction.splitContraction_product

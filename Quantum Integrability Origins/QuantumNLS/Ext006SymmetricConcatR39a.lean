import QuantumNLS.Ext006OccupationConcatR39a

/-! Removal of the inner left symmetrization in actual completed tensors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SymmetricConcatR39a
open TensorCarrier Ext006PairPowerWick
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Extend a permutation by the identity on the second block. -/
def leftPerm {k : ℕ} (m : ℕ) (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k+m)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr σ (Equiv.refl (Fin m))).trans finSumFinEquiv)

lemma concat_perm_left {k m : ℕ} (σ : Equiv.Perm (Fin k))
    (x : HilbertTensorPower ℂ E k) (y : HilbertTensorPower ℂ E m) :
    concat (permHilbertIsometry σ x) y = permHilbertIsometry (leftPerm m σ) (concat x y) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    have hc1 := (concatRightMap (E := E) (k := k) (m := m) y).continuous.comp
      (permHilbertIsometry (𝕜 := ℂ) (E := E) σ).continuous
    have hc2 := (permHilbertIsometry (𝕜 := ℂ) (E := E) (leftPerm m σ)).continuous.comp
      (concatRightMap (E := E) (k := k) (m := m) y).continuous
    simpa only [Function.comp_apply, concatRightMap_apply] using isClosed_eq hc1 hc2
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod c f =>
      simp only [UniformSpace.Completion.coe_smul, map_smul, concat_smul_left]
      congr 1
      induction y using UniformSpace.Completion.induction_on with
      | hp =>
        let x : HilbertTensorPower ℂ E k := ((ptprod f : AlgTensorPower ℂ E k) : _)
        have hc1 := (concatLeftMap (E := E) (k := k) (m := m)
          (permHilbertIsometry σ x)).continuous
        have hc2 := (permHilbertIsometry (𝕜 := ℂ) (E := E) (leftPerm m σ)).continuous.comp
          (concatLeftMap (E := E) (k := k) (m := m) x).continuous
        simpa only [Function.comp_apply, concatLeftMap_apply] using isClosed_eq hc1 hc2
      | ih a =>
        induction a using AlgTensorPower.induction_on with
        | smul_ptprod d g =>
          simp only [UniformSpace.Completion.coe_smul, map_smul, concat_smul_right,
            permHilbertIsometry_coe, permLinearEquiv_ptprod, concat_ptprod]
          have he : Fin.append (fun i => f (σ.symm i)) g =
              (fun i => Fin.append f g ((leftPerm m σ).symm i)) := by
            funext i
            refine Fin.addCases (fun j => ?_) (fun j => ?_) i
            · simp [leftPerm]
            · simp [leftPerm]
          exact congrArg (fun h : Fin (k+m) → E => d •
            ((ptprod h : AlgTensorPower ℂ E (k+m)) : HilbertTensorPower ℂ E (k+m))) he
        | add a b ha hb =>
          simp only [UniformSpace.Completion.coe_add, map_add, concat_add_right, ha, hb]
    | add a b ha hb =>
      simp only [UniformSpace.Completion.coe_add, map_add, concat_add_left, ha, hb]

/-- Inner symmetrization can be removed before the final symmetrization.
This holds for arbitrary completed tensors and arbitrary block sizes. -/
theorem symProj_concat_symProj_left {k m : ℕ} (x : HilbertTensorPower ℂ E k)
    (y : HilbertTensorPower ℂ E m) :
    symProj ℂ E (k+m) (concat (symProj ℂ E k x) y) =
      symProj ℂ E (k+m) (concat x y) := by
  classical
  let C := concatRightMap (E := E) (k := k) (m := m) y
  rw [← concatRightMap_apply (symProj ℂ E k x) y]
  change symProj ℂ E (k+m) (C (symProj ℂ E k x)) = _
  rw [symProj_eq_factorial_average (𝕜 := ℂ) (E := E) k]
  simp only [smul_apply, sum_apply, map_smul, map_sum]
  have hs : ∀ σ : Equiv.Perm (Fin k),
      symProj ℂ E (k+m) (C ((permRep ℂ E k σ : _ →L[ℂ] _) x)) =
        symProj ℂ E (k+m) (concat x y) := by
    intro σ
    rw [show C ((permRep ℂ E k σ : _ →L[ℂ] _) x) =
      concat (permHilbertIsometry σ x) y from concatRightMap_apply _ _,
      concat_perm_left, symProj_perm]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k),
    one_smul]

/-- Tensor transport commutes with literal completed tensor concatenation. -/
lemma tensorPower_concat {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) {k m : ℕ} (x : HilbertTensorPower ℂ E k)
    (y : HilbertTensorPower ℂ E m) :
    TensorFourier.tensorPower e (k+m) (concat x y) =
      concat (TensorFourier.tensorPower e k x) (TensorFourier.tensorPower e m y) := by
  apply (splitIsometry (𝕜 := ℂ) (E := F) k m).injective
  rw [TensorFourier.tensorPower_split, concat, LinearIsometryEquiv.apply_symm_apply,
    htmap_htmul, concat, LinearIsometryEquiv.apply_symm_apply]
  rfl

end QuantumNLS.Ext006SymmetricConcatR39a

#print axioms QuantumNLS.Ext006SymmetricConcatR39a.symProj_concat_symProj_left

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SymmetricConcatR39a." then
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
  Lean.logInfo m!"Round39a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."

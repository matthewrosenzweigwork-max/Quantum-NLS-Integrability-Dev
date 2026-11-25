import QuantumNLS.Prop022ClassicalTimeR116
import QuantumNLS.Ext006PairPowerWick

/-! The real symmetric-power differential equals the literal symmetric
insertion with its exact degree factor. This is a prerequisite to Hessian
identification, not the Hessian identification itself. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace Topology ContDiff
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
namespace QuantumNLS.Prop022SymmetricSlotR117
open TensorCarrier PhysicalTensor BetheCoefficientTransform
open Prop022TensorCompressionR115 Prop022TensorCalculusR116 Prop022ClassicalTimeR116
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup
local instance (n : ℕ) : AddCommGroup (HilbertTensorPower ℂ (L2T L) n) :=
  (inferInstance : NormedAddCommGroup (HilbertTensorPower ℂ (L2T L) n)).toAddCommGroup

lemma projected_slots_eq (m : ℕ) (u h : L2T L) (i j : Fin m) :
    (physSector L m).orthogonalProjectionOnto
      (tensorMultilinear m (Function.update (fun _ => u) i h)) =
    (physSector L m).orthogonalProjectionOnto
      (tensorMultilinear m (Function.update (fun _ => u) j h)) := by
  classical
  apply Subtype.ext
  rw [← Submodule.starProjection_apply, ← Submodule.starProjection_apply,
    ← symProj_eq_starProjection, tensorMultilinear_apply, tensorMultilinear_apply]
  have hf : (fun a => Function.update (fun _ => u) i h ((Equiv.swap i j).symm a)) =
      Function.update (fun _ => u) j h := by
    simpa only [Equiv.symm_swap, Equiv.swap_apply_right, Function.comp_def] using
      (Function.update_comp_eq_of_injective (fun _ : Fin m => u)
        (Equiv.swap i j).injective j h)
  have hp := Ext006PairPowerWick.symProj_perm (E := L2T L) (Equiv.swap i j)
    ((ptprod (Function.update (fun _ => u) i h) : AlgTensorPower ℂ (L2T L) m) :
      HilbertTensorPower ℂ (L2T L) m)
  rw [permHilbertIsometry_coe, permLinearEquiv_ptprod, hf] at hp
  exact hp.symm

lemma insertion_one_slot (r : ℕ) (u h : L2T L) :
    insertion r 1 u (power 1 h) = (physSector L (r+1)).orthogonalProjectionOnto
      (tensorMultilinear (r+1) (Function.update (fun _ => u) (Fin.last r) h)) := by
  classical
  have hf : Fin.append (fun _ : Fin r => u) (fun _ : Fin 1 => h) =
      Function.update (fun _ : Fin (r+1) => u) (Fin.last r) h := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hn : j.castAdd 1 ≠ Fin.last r := by
        exact Fin.ne_of_val_ne (by change (j : ℕ) ≠ r; omega)
      simp [hn]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hi : Fin.natAdd r (0 : Fin 1) = Fin.last r := by
        apply Fin.ext
        simp
      rw [Fin.append_right, hi, Function.update_self]
  change (physSector L (r+1)).orthogonalProjectionOnto
    ((splitIsometry r 1).symm (htmul (htpow r u) (htpow 1 h))) = _
  rw [htpow, htpow, ← splitIsometry_ptprod_append, LinearIsometryEquiv.symm_apply_apply,
    tensorMultilinear_apply, hf]

/-- The slot sum is exactly m times the symmetric one-slot insertion. -/
theorem powerD_eq_insertion (r : ℕ) (u h : L2T L) :
    powerD (r+1) u h = ((r+1 : ℕ) : ℝ) • insertion r 1 u (power 1 h) := by
  classical
  change (physSector L (r+1)).orthogonalProjectionOnto
    (powerDifferential (r+1) u h) = _
  rw [powerDifferential, sum_apply, map_sum]
  have he (i : Fin (r+1)) :
      (physSector L (r+1)).orthogonalProjectionOnto
        (((tensorMultilinear (L := L) (r+1)).restrictScalars ℝ).toContinuousLinearMap
          (fun _ => u) i h) = insertion r 1 u (power 1 h) := by
    change (physSector L (r+1)).orthogonalProjectionOnto
      (tensorMultilinear (r+1) (Function.update (fun _ => u) i h)) = _
    rw [projected_slots_eq (r+1) u h i (Fin.last r), ← insertion_one_slot]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul ℝ (r+1) _).symm
end QuantumNLS.Prop022SymmetricSlotR117
#print axioms QuantumNLS.Prop022SymmetricSlotR117.projected_slots_eq
#print axioms QuantumNLS.Prop022SymmetricSlotR117.powerD_eq_insertion

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022SymmetricSlotR117." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022SymmetricSlotR117." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R117 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

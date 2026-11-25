import QuantumNLS.Ext006StrongVacuumR33a

/-! Adjointness of arbitrary l2 smeared fields on the invariant smooth
number domain. The joint summation is proved absolutely summable before
reindexing. No covariance, Gram matrix or implementer is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SmearedAdjointR34a
open Occupation Ext006VacuumRecurrence Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmearedDomainR33a Ext006BogoliubovAlg

lemma norm_square_summable {I : Type*} (v : lp (fun _ : I => ℂ) 2) :
    Summable (fun i => ‖v i‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.hasSum_norm (p := 2) (by norm_num) v).summable

/-- Absolute convergence of the joint pairing prior to either iterated sum. -/
lemma joint_pairing_summable (h : H) (v w : Fock) (hw : Smooth w) :
    Summable (fun z : Occ × ℤ => inner ℂ (h z.2*v z.1) (annCoeff z.2 w z.1)) := by
  have ha : Memℓp (fun z : Occ × ℤ => h z.2*v z.1) 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, mul_pow, mul_comm] using
      (norm_square_summable v).mul_of_nonneg (norm_square_summable h)
        (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  have hb : Memℓp (fun z : Occ × ℤ => annCoeff z.2 w z.1) 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, pow_zero, one_mul] using
      ann_double_summable w hw 0
  exact lp.summable_inner ⟨_,ha⟩ ⟨_,hb⟩

lemma shifted_pairing (h : H) (v w : Fock) (m : Occ) (a : ℤ) :
    inner ℂ (h a*creCoeff a v (m+e a)) (w (m+e a)) =
      inner ℂ (h a*v m) (annCoeff a w m) := by
  rw [creCoeff_add, annCoeff]
  simp [RCLike.inner_apply, mul_comm, mul_left_comm, mul_assoc]

lemma pairing_off (h : H) (v w : Fock) (z : Occ × ℤ)
    (hz : z ∉ Set.range (fun y : Occ × ℤ => (y.1+e y.2,y.2))) :
    inner ℂ (h z.2*creCoeff z.2 v z.1) (w z.1) = 0 := by
  have hn : z.1 ∉ Set.range (fun m : Occ => m+e z.2) := by
    rintro ⟨m,hm⟩
    exact hz ⟨(m,z.2),Prod.ext hm rfl⟩
  rw [creCoeff_off z.2 v z.1 hn, mul_zero, inner_zero_left]

/-- Adjoint pairing for all l2 smearings, including infinite support. -/
theorem adjoint_pairing (h : H) (v w : Fock) (hv : Smooth v) (hw : Smooth w) :
    inner ℂ v (smearedAnn h w hw) = inner ℂ (smearedCre h v hv) w := by
  let A : Occ × ℤ → ℂ := fun z => inner ℂ (h z.2*v z.1) (annCoeff z.2 w z.1)
  let B : Occ × ℤ → ℂ := fun z => inner ℂ (h z.2*creCoeff z.2 v z.1) (w z.1)
  let shift : Occ × ℤ → Occ × ℤ := fun z => (z.1+e z.2,z.2)
  have he : B ∘ shift = A := by
    funext z
    exact shifted_pairing h v w z.1 z.2
  have hA : Summable A := joint_pairing_summable h v w hw
  have hB : Summable B := (shift_pair_injective.summable_iff (pairing_off h v w)).mp
    (by rw [he]; exact hA)
  have hsum : ∑' z, A z = ∑' z, B z := by
    rw [← he]
    exact shift_pair_injective.tsum_eq (fun z hz => by
      by_contra hn
      exact hz (pairing_off h v w z hn))
  calc
    inner ℂ v (smearedAnn h w hw) = ∑' m : Occ, ∑' a : ℤ, A (m,a) := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro m
      change inner ℂ (v m) (inner ℂ h (xvec w m)) = _
      rw [lp.inner_eq_tsum, RCLike.inner_apply, ← tsum_mul_right]
      apply tsum_congr
      intro a
      simp [A, RCLike.inner_apply, Ext006QuasifreeWeak.xvec, Ext006QuasifreeWeak.xcoord,
        annCoeff, mul_assoc, mul_comm, mul_left_comm]
    _ = ∑' z, A z := hA.tsum_prod.symm
    _ = ∑' z, B z := hsum
    _ = ∑' m : Occ, ∑' a : ℤ, B (m,a) := hB.tsum_prod
    _ = inner ℂ (smearedCre h v hv) w := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro m
      rw [tsum_eq_sum (s := m.support) (fun a ha => by
        have hz : m a = 0 := by simpa using ha
        simp [B,creCoeff,hz])]
      change _ = inner ℂ (smearedCreCoeff h v m) (w m)
      rw [smearedCreCoeff, sum_inner]

/-- The reverse adjoint pairing follows with the complex convention intact. -/
theorem adjoint_pairing_rev (h : H) (v w : Fock) (hv : Smooth v) (hw : Smooth w) :
    inner ℂ v (smearedCre h w hw) = inner ℂ (smearedAnn h v hv) w := by
  have he := congrArg (starRingEnd ℂ) (adjoint_pairing h w v hw hv)
  simpa only [inner_conj_symm] using he.symm

end QuantumNLS.Ext006SmearedAdjointR34a

#print axioms QuantumNLS.Ext006SmearedAdjointR34a.joint_pairing_summable
#print axioms QuantumNLS.Ext006SmearedAdjointR34a.adjoint_pairing
#print axioms QuantumNLS.Ext006SmearedAdjointR34a.adjoint_pairing_rev

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SmearedAdjointR34a." then
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
  Lean.logInfo m!"Round34a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."

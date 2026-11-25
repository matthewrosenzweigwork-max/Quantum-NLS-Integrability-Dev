import QuantumNLS.Ext006FieldClosureR42a

/-! Finite-particle estimates for the ACTUAL smeared field, with arbitrary
square-summable smearing. These estimates are not a postulated exponential. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006FieldBoundsR42a
open Occupation Ext006BogoliubovAlg Ext006QuasifreeWeak Ext006VacuumRecurrence
open Ext006ModeDomainR33a Ext006SmearedDomainR33a Ext006SmoothOperatorsR34a
open Ext006IdentityCyclicR35a Ext006StrongFieldR41a

/-- Bounded particle support does not require finite mode support. -/
def ParticleBound (N : ℕ) (v : Fock) : Prop := ∀ m : Occ, N < total m → v m = 0

lemma xvec_norm_mass (v : D) :
    (∑' m : Occ, ‖xvec v.1 m‖^2) = ∑' m : Occ, (total m : ℝ)*‖v.1 m‖^2 := by
  have ha : Summable (fun z : Occ × ℤ => ‖annCoeff z.2 v.1 z.1‖^2) := by
    simpa only [pow_zero,one_mul] using ann_double_summable v.1 v.2 0
  have hc : Summable (fun z : Occ × ℤ => (z.1 z.2 : ℝ)*‖v.1 z.1‖^2) := by
    simpa only [pow_zero,one_mul] using count_summable v.2 0
  have hoff (z : Occ × ℤ) (hz : z ∉ Set.range (fun y : Occ × ℤ => (y.1+e y.2,y.2))) :
      (z.1 z.2 : ℝ)*‖v.1 z.1‖^2 = 0 := by
    have he : z.1 z.2 = 0 := by
      by_contra hn
      exact hz ⟨(z.1-e z.2,z.2),Prod.ext (shift_sub_add (Nat.one_le_iff_ne_zero.mpr hn)) rfl⟩
    simp only [he,Nat.cast_zero,zero_mul]
  calc
    _ = ∑' m : Occ, ∑' a : ℤ, ‖annCoeff a v.1 m‖^2 := by
      apply tsum_congr
      intro m
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two,xvec_apply,xcoord,annCoeff] using
        ((lp.hasSum_norm (p := 2) (by norm_num) (xvec v.1 m)).tsum_eq).symm
    _ = ∑' z : Occ × ℤ, ‖annCoeff z.2 v.1 z.1‖^2 := ha.tsum_prod.symm
    _ = ∑' z : Occ × ℤ, ((z.1+e z.2) z.2 : ℝ)*‖v.1 (z.1+e z.2)‖^2 := by
      apply tsum_congr
      intro z
      simp only [annCoeff,Finsupp.add_apply,Finsupp.single_eq_same,Nat.cast_add,Nat.cast_one]
      exact norm_sq_sqrt_mul _ (by positivity) _
    _ = ∑' z : Occ × ℤ, (z.1 z.2 : ℝ)*‖v.1 z.1‖^2 := shift_pair_injective.tsum_eq (fun z hz => by
      by_contra hn
      exact hz (hoff z hn))
    _ = ∑' m : Occ, ∑' a : ℤ, (m a : ℝ)*‖v.1 m‖^2 := hc.tsum_prod
    _ = _ := by simp only [tsum_mul_right,occupation_tsum]

lemma A_norm_sq_le_mass (h : H) (v : D) :
    ‖(A h v).1‖^2 ≤ ‖h‖^2 * ∑' m : Occ, (total m : ℝ)*‖v.1 m‖^2 := by
  have ha : Summable (fun z : Occ × ℤ => ‖annCoeff z.2 v.1 z.1‖^2) := by
    simpa only [pow_zero,one_mul] using ann_double_summable v.1 v.2 0
  have hx : Summable (fun m : Occ => ‖xvec v.1 m‖^2) := by
    convert ha.prod using 1
    funext m
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,xvec_apply,xcoord,annCoeff] using
      ((lp.hasSum_norm (p := 2) (by norm_num) (xvec v.1 m)).tsum_eq).symm
  have hl : Summable (fun m : Occ => ‖((A h v).1) m‖^2) := summable_sq (A h v).1
  have hlEq := (lp.hasSum_norm (p := 2) (by norm_num) (A h v).1).tsum_eq
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hlEq
  rw [← hlEq,← xvec_norm_mass v,← tsum_mul_left]
  apply Summable.tsum_le_tsum ?_ hl (hx.mul_left (‖h‖^2))
  intro m
  change ‖inner ℂ h (xvec v.1 m)‖^2 ≤ _
  have hb : ‖inner ℂ h (xvec v.1 m)‖ ≤ ‖h‖*‖xvec v.1 m‖ := norm_inner_le_norm _ _
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2

lemma A_adjoint (h : H) (v w : D) :
    inner ℂ v.1 (A h w).1 = inner ℂ (C h v).1 w.1 := by
  simpa only [B,Bstar,C_zero,A_zero,add_zero] using B_adjoint h 0 v w

lemma C_adjoint (h : H) (v w : D) :
    inner ℂ v.1 (C h w).1 = inner ℂ (A h v).1 w.1 := by
  simpa only [B,Bstar,C_zero,A_zero,zero_add] using B_adjoint 0 h v w

/-- Exact creation/annihilation norm identity, derived from the actual CCR. -/
theorem C_norm_sq (h : H) (v : D) :
    ‖(C h v).1‖^2 = ‖(A h v).1‖^2 + ‖h‖^2*‖v.1‖^2 := by
  have he := congrArg (fun w : D => inner ℂ v.1 w.1) (LinearMap.congr_fun (AC h h) v)
  change inner ℂ v.1 ((A h (C h v)).1-(C h (A h v)).1) =
    inner ℂ v.1 ((inner ℂ h h) • v.1) at he
  rw [inner_sub_right,inner_smul_right,A_adjoint h v (C h v),C_adjoint h v (A h v)] at he
  have hr := congrArg Complex.re he
  simp only [inner_self_eq_norm_sq_to_K] at hr
  norm_cast at hr
  change ‖(C h v).1‖^2 - ‖(A h v).1‖^2 = ‖h‖^2*‖v.1‖^2 at hr
  linarith only [hr]

lemma particle_mass_le {N : ℕ} (v : D) (hv : ParticleBound N v.1) :
    (∑' m : Occ, (total m : ℝ)*‖v.1 m‖^2) ≤ (N : ℝ)*‖v.1‖^2 := by
  have hs : Summable (fun m : Occ => (total m : ℝ)*‖v.1 m‖^2) := by
    have ht := ((summable_prod_of_nonneg (fun z : Occ × ℤ => by positivity)).mp
      (count_summable v.2 0)).2
    simpa only [pow_zero,one_mul,tsum_mul_right,occupation_tsum] using ht
  rw [← (by simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    (lp.hasSum_norm (p := 2) (by norm_num) v.1).tsum_eq : (∑' m : Occ, ‖v.1 m‖^2) = ‖v.1‖^2),← tsum_mul_left]
  apply Summable.tsum_le_tsum ?_ hs ((summable_sq v.1).mul_left (N : ℝ))
  intro m
  by_cases hm : N < total m
  · simp only [hv m hm,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_not_gt hm) (sq_nonneg _)

theorem A_norm_sq_le {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) :
    ‖(A h v).1‖^2 ≤ ‖h‖^2*(N : ℝ)*‖v.1‖^2 := by
  calc
    _ ≤ ‖h‖^2*((N : ℝ)*‖v.1‖^2) := (A_norm_sq_le_mass h v).trans
      (mul_le_mul_of_nonneg_left (particle_mass_le v hv) (sq_nonneg _))
    _ = _ := by ring

theorem C_norm_sq_le {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) :
    ‖(C h v).1‖^2 ≤ ‖h‖^2*((N : ℝ)+1)*‖v.1‖^2 := by
  rw [C_norm_sq]
  have he := A_norm_sq_le h v hv
  nlinarith

/-- The standard finite-particle field estimate on the actual smooth carrier. -/
theorem field_norm_sq_le {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) :
    ‖(field h v).1‖^2 ≤ 4*‖h‖^2*((N : ℝ)+1)*‖v.1‖^2 := by
  have hn : ‖(field h v).1‖ ≤ ‖(A h v).1‖+‖(C h v).1‖ := norm_add_le _ _
  have ha := A_norm_sq_le h v hv
  have hc := C_norm_sq_le h v hv
  have hs := sq_nonneg (‖(A h v).1‖-‖(C h v).1‖)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [mul_nonneg (sq_nonneg ‖h‖) (sq_nonneg ‖v.1‖)]

lemma A_particleBound {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) :
    ParticleBound N (A h v).1 := by
  intro m hm
  have hx : xvec v.1 m = 0 := by
    apply lp.ext
    funext a
    change (Real.sqrt ((m a : ℝ)+1) : ℂ)*v.1 (m+e a) = 0
    rw [hv (m+e a) (by rw [total_add_e]; omega),mul_zero]
  change inner ℂ h (xvec v.1 m) = 0
  rw [hx,inner_zero_right]

lemma C_particleBound {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) :
    ParticleBound (N+1) (C h v).1 := by
  intro m hm
  change (∑ a ∈ m.support, h a*creCoeff a v.1 m) = 0
  apply Finset.sum_eq_zero
  intro a ha
  have ht := total_sub_e (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp ha))
  rw [creCoeff,hv (m-e a) (by omega),mul_zero,mul_zero]

lemma field_particleBound {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) :
    ParticleBound (N+1) (field h v).1 := by
  intro m hm
  change (A h v).1 m + (C h v).1 m = 0
  rw [A_particleBound h v hv m (by omega),C_particleBound h v hv m hm,zero_add]

theorem field_power_particleBound {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) (n : ℕ) :
    ParticleBound (N+n) (((field h)^n) v).1 := by
  induction n with
  | zero => simpa only [Nat.add_zero,pow_zero,Module.End.one_apply] using hv
  | succ n ih =>
    simpa only [pow_succ',Module.End.mul_apply,Nat.add_assoc] using
      field_particleBound h (((field h)^n) v) ih

/-- Factorial-square estimate for every field iterate on bounded-particle
vectors. It retains the square-root factorial gain needed for analyticity. -/
theorem field_power_norm_sq_le {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) (n : ℕ) :
    ‖(((field h)^n) v).1‖^2 ≤
      (4*‖h‖^2)^n * ((N+n).factorial : ℝ) / (N.factorial : ℝ) * ‖v.1‖^2 := by
  induction n with
  | zero =>
    have hf : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
    simp only [pow_zero,Module.End.one_apply,Nat.add_zero,one_mul,div_self hf]
    exact le_rfl
  | succ n ih =>
    rw [pow_succ' (field h) n]
    change ‖(field h (((field h)^n) v)).1‖^2 ≤ _
    calc
      _ ≤ 4*‖h‖^2*((((N+n : ℕ) : ℝ))+1)*‖(((field h)^n) v).1‖^2 :=
        field_norm_sq_le h (((field h)^n) v) (field_power_particleBound h v hv n)
      _ ≤ 4*‖h‖^2*((((N+n : ℕ) : ℝ))+1)*
          ((4*‖h‖^2)^n * ((N+n).factorial : ℝ) / (N.factorial : ℝ) * ‖v.1‖^2) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by
        simp only [pow_succ,Nat.add_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,Nat.cast_add]
        ring

end QuantumNLS.Ext006FieldBoundsR42a
#print axioms QuantumNLS.Ext006FieldBoundsR42a.xvec_norm_mass
#print axioms QuantumNLS.Ext006FieldBoundsR42a.C_norm_sq
#print axioms QuantumNLS.Ext006FieldBoundsR42a.field_norm_sq_le
#print axioms QuantumNLS.Ext006FieldBoundsR42a.field_power_norm_sq_le

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006FieldBoundsR42a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Round42a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."

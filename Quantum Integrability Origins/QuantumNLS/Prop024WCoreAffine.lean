import QuantumNLS.Prop024WCoordinates

/-! PROP-024 affine Weyl action, module 2: the affine identity on the finite-particle core.

For the frozen EXT-006 unitary `unitary h t = exp(i t (a*(h) + a(h)))` on the occupation Fock
space and a finite-particle vector `x ∈ D` (`ParticleBound N`), the frozen entire series
`unitary h t x = ∑ₙ exponentialTerm h t x n` is differentiated through the bounded coordinate
functionals of module 1, using only the proved CCR commutators of the frozen smooth-domain
operators `A`, `C`:

  `(a(g) U_t x)_m = (U_t a(g) x)_m + (i t ⟨g,h⟩) (U_t x)_m`,
  `(a*(g) U_t x)_m = (U_t a*(g) x)_m + (i t (-⟨h,g⟩)) (U_t x)_m`.

No Weyl/interaction compatibility premise and no smoothness of `U_t x` is assumed; smoothness
and the extension to all of `D` are proved in later modules. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Prop024WCoreAffine
open Occupation Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmoothOperatorsR34a Ext006FieldBoundsR42a Ext006StrongFieldR41a
open Ext006AnalyticFieldR42a Ext006EntireFieldR43a Ext006ExponentialInnerR43a
open Ext006BoundedExponentialR43a Ext006SeriesIdentificationR43a Prop024WCoordinates

/-- If `[X,F] = c`, then `X F^(n+1) = F^(n+1) X + (n+1) c F^n`. -/
lemma comm_pow {R : Type*} [Ring R] [Algebra ℂ R] (X F : R) (c : ℂ)
    (h : X * F - F * X = c • (1 : R)) (n : ℕ) :
    X * F^(n+1) = F^(n+1) * X + (((n : ℂ)+1) * c) • F^n := by
  have hXF : X * F = F * X + c • (1 : R) := by rw [← h]; abel
  induction n with
  | zero => simpa using hXF
  | succ n ih =>
    calc
      X * F^(n+1+1) = (X * F^(n+1)) * F := by rw [pow_succ F (n+1), mul_assoc]
      _ = (F^(n+1) * X + (((n : ℂ)+1) * c) • F^n) * F := by rw [ih]
      _ = F^(n+1) * (X * F) + (((n : ℂ)+1) * c) • F^(n+1) := by
          rw [add_mul, mul_assoc, smul_mul_assoc, ← pow_succ]
      _ = F^(n+1) * (F * X + c • (1 : R)) + (((n : ℂ)+1) * c) • F^(n+1) := by rw [hXF]
      _ = F^(n+1+1) * X + ((((n+1 : ℕ) : ℂ)+1) * c) • F^(n+1) := by
          rw [mul_add, ← mul_assoc, ← pow_succ, mul_smul_comm, mul_one, add_assoc,
            ← add_smul]
          congr 2
          push_cast
          ring

/-- `[a(g), φ(h)] = ⟨g,h⟩` on the frozen smooth domain. -/
lemma A_field_comm (g h : H) :
    A g * field h - field h * A g = (inner ℂ g h) • (1 : Module.End ℂ D) := by
  have h1 := AC g h
  have h2 := AA g h
  have : A g * field h - field h * A g =
      (A g * A h - A h * A g) + (A g * C h - C h * A g) := by
    unfold field; noncomm_ring
  rw [this, h1, sub_eq_zero.mpr h2, zero_add]

/-- `[a*(g), φ(h)] = -⟨h,g⟩` on the frozen smooth domain. -/
lemma C_field_comm (g h : H) :
    C g * field h - field h * C g = (-(inner ℂ h g)) • (1 : Module.End ℂ D) := by
  have h1 := AC h g
  have h2 := CC g h
  have : C g * field h - field h * C g =
      -(A h * C g - C g * A h) + (C g * C h - C h * C g) := by
    unfold field; noncomm_ring
  rw [this, h1, sub_eq_zero.mpr h2, add_zero]
  exact (neg_smul (inner ℂ h g) (1 : Module.End ℂ D)).symm

/-- General finite-particle commutator lemma: if `X` has coordinate functional `ℓ` at `m`,
`[X,φ(h)] = c0`, and `X` maps `ParticleBound N` to `ParticleBound N'`, then the series gives
`ℓ(U_t x) = (U_t X x)_m + (i t c0) (U_t x)_m`. -/
theorem core_comm {N N' : ℕ} (X : Module.End ℂ D) (ℓ : Fock →L[ℂ] ℂ) (m : Occ)
    (hℓ : ∀ y : D, ℓ y.1 = (X y).1 m) (h : H) (c0 : ℂ)
    (hc : X * field h - field h * X = c0 • (1 : Module.End ℂ D))
    (hX : ∀ y : D, ParticleBound N y.1 → ParticleBound N' (X y).1)
    (t : ℝ) (x : D) (hx : ParticleBound N x.1) :
    ℓ (unitary h t x.1) =
      (unitary h t (X x).1) m + (Complex.I * (t : ℂ) * c0) * (unitary h t x.1) m := by
  have hXx : ParticleBound N' (X x).1 := hX x hx
  have hUx : unitary h t x.1 = ∑' n, exponentialTerm h t x n :=
    unitary_core h t ⟨x, ⟨N, hx⟩⟩
  have hUX : unitary h t (X x).1 = ∑' n, exponentialTerm h t (X x) n :=
    unitary_core h t ⟨X x, ⟨N', hXx⟩⟩
  have hU : HasSum (fun n => exponentialTerm h t x n) (unitary h t x.1) := by
    rw [hUx]; exact (entire_summable h t x hx).hasSum
  have hUX' : HasSum (fun n => exponentialTerm h t (X x) n) (unitary h t (X x).1) := by
    rw [hUX]; exact (entire_summable h t (X x) hXx).hasSum
  let ev : Fock →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : Occ => ℂ) 2 m
  have h1 : HasSum (fun n => (exponentialTerm h t (X x) n) m) ((unitary h t (X x).1) m) :=
    hUX'.mapL ev
  have h2 : HasSum (fun n => (exponentialTerm h t x n) m) ((unitary h t x.1) m) :=
    hU.mapL ev
  set c : ℂ := Complex.I * (t : ℂ) * c0 with hcdef
  have hu : ∀ n : ℕ, ℓ (exponentialTerm h t x (n+1)) =
      (exponentialTerm h t (X x) (n+1)) m + c * (exponentialTerm h t x n) m := by
    intro n
    have hpow := congrArg (fun Y : Module.End ℂ D => (Y x).1 m)
      (comm_pow (X) (field h) c0 hc n)
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Submodule.coe_add, Submodule.coe_smul, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at hpow
    simp only [exponentialTerm, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [hℓ, hpow]
    have hf : ((n+1).factorial : ℂ) = ((n : ℂ)+1) * (n.factorial : ℂ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hn0 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hn1 : ((n : ℂ)+1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [hf, hcdef]
    field_simp
    ring
  have h3 : HasSum (fun n => ℓ (exponentialTerm h t x (n+1)))
      (((unitary h t (X x).1) m - ∑ i ∈ Finset.range 1, (exponentialTerm h t (X x) i) m) +
        c * (unitary h t x.1) m) := by
    have := ((hasSum_nat_add_iff' 1).mpr h1).add (h2.mul_left c)
    have hfun : (fun n => ℓ (exponentialTerm h t x (n+1))) =
        fun n => (exponentialTerm h t (X x) (n+1)) m + c * (exponentialTerm h t x n) m :=
      funext hu
    rw [hfun]
    exact this
  have h0 : ℓ (exponentialTerm h t x 0) = (exponentialTerm h t (X x) 0) m := by
    simp [exponentialTerm, hℓ]
  have h4 : HasSum (fun n => ℓ (exponentialTerm h t x n))
      ((unitary h t (X x).1) m + c * (unitary h t x.1) m) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, h0]
    simp only [Finset.sum_range_one] at h3
    convert h3 using 1
    ring
  exact (hU.mapL ℓ).unique h4

/-- Annihilation coordinate identity on finite-particle vectors. -/
theorem core_ann {N : ℕ} (g h : H) (t : ℝ) (x : D) (hx : ParticleBound N x.1) (m : Occ) :
    annC g m (unitary h t x.1) =
      (unitary h t (A g x).1) m + (Complex.I * (t : ℂ) * inner ℂ g h) * (unitary h t x.1) m :=
  core_comm (N := N) (N' := N) (A g) (annC g m) m (fun y => (A_coord g y m).symm) h
    (inner ℂ g h) (A_field_comm g h) (fun y hy => A_particleBound g y hy) t x hx

/-- Creation coordinate identity on finite-particle vectors. -/
theorem core_cre {N : ℕ} (g h : H) (t : ℝ) (x : D) (hx : ParticleBound N x.1) (m : Occ) :
    creC g m (unitary h t x.1) =
      (unitary h t (C g x).1) m +
        (Complex.I * (t : ℂ) * (-(inner ℂ h g))) * (unitary h t x.1) m :=
  core_comm (N := N) (N' := N+1) (C g) (creC g m) m (fun y => (C_coord g y m).symm) h
    (-(inner ℂ h g)) (C_field_comm g h) (fun y hy => C_particleBound g y hy) t x hx

end QuantumNLS.Prop024WCoreAffine

#print axioms QuantumNLS.Prop024WCoreAffine.comm_pow
#print axioms QuantumNLS.Prop024WCoreAffine.core_comm
#print axioms QuantumNLS.Prop024WCoreAffine.core_ann
#print axioms QuantumNLS.Prop024WCoreAffine.core_cre

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WCoreAffine." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WCoreAffine." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"Prop024WCoreAffine aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."

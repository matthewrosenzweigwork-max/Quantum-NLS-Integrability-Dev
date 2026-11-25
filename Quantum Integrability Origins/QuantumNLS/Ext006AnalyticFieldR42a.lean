import QuantumNLS.Ext006FieldBoundsR42a

/-! Actual local field-exponential series on every bounded-particle vector.
No self-adjoint extension, bounded Weyl operator, or Weyl uniqueness is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006AnalyticFieldR42a
open Occupation Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a Ext006StrongFieldR41a
open Ext006IdentityCyclicR35a Ext006FieldBoundsR42a
open Ext006CreationGramR34a Ext006CoreTransportR35a Ext006KernelHilbertSchmidt

lemma field_norm_le {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) :
    ‖(field h v).1‖ ≤ 2*‖h‖*((N : ℝ)+1)*‖v.1‖ := by
  have hb := field_norm_sq_le h v hv
  have hp : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have haux : 0 ≤ 4*‖h‖^2*‖v.1‖^2*(N : ℝ)*((N : ℝ)+1) := by positivity
  have hr : 0 ≤ 2*‖h‖*((N : ℝ)+1)*‖v.1‖ := by positivity
  nlinarith [norm_nonneg (field h v).1]

/-- A coarse factorial estimate supplies an explicit positive analytic radius. -/
theorem field_power_norm_le {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) (n : ℕ) :
    ‖(((field h)^n) v).1‖ ≤ (2*‖h‖*((N : ℝ)+1))^n*(n.factorial : ℝ)*‖v.1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (field h) n]
    change ‖(field h (((field h)^n) v)).1‖ ≤ _
    have hb := field_norm_le h (((field h)^n) v) (field_power_particleBound h v hv n)
    have hn : ((N+n : ℕ) : ℝ)+1 ≤ ((N : ℝ)+1)*((n : ℝ)+1) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) N,Nat.cast_nonneg (α := ℝ) n]
    calc
      _ ≤ 2*‖h‖*((((N+n : ℕ) : ℝ))+1)*‖(((field h)^n) v).1‖ := hb
      _ ≤ (2*‖h‖*((N : ℝ)+1)*((n : ℝ)+1))*
          ((2*‖h‖*((N : ℝ)+1))^n*(n.factorial : ℝ)*‖v.1‖) := by
        apply mul_le_mul ?_ ih (norm_nonneg _) (by positivity)
        have he := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*‖h‖ by positivity)
        simpa only [mul_assoc] using he
      _ = _ := by
        rw [pow_succ,Nat.factorial_succ]
        push_cast
        ring

/-- Literal exponential summand of the ACTUAL smeared field. -/
def exponentialTerm (h : H) (t : ℝ) (v : D) (n : ℕ) : Fock :=
  ((Complex.I*(t : ℂ))^n/(n.factorial : ℂ)) • (((field h)^n) v).1

lemma exponentialTerm_norm_le {N : ℕ} (h : H) (t : ℝ) (v : D)
    (hv : ParticleBound N v.1) (n : ℕ) :
    ‖exponentialTerm h t v n‖ ≤ (2*‖h‖*((N : ℝ)+1)*|t|)^n*‖v.1‖ := by
  have hb := field_power_norm_le h v hv n
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : ‖(Complex.I*(t : ℂ))^n/(n.factorial : ℂ)‖ = |t|^n/(n.factorial : ℝ) := by
    simp only [norm_div,norm_pow,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,
      Real.norm_eq_abs,Complex.norm_natCast]
  rw [exponentialTerm,norm_smul,hn]
  calc
    _ ≤ (|t|^n/(n.factorial : ℝ))*
        ((2*‖h‖*((N : ℝ)+1))^n*(n.factorial : ℝ)*‖v.1‖) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by simp only [mul_pow]; field_simp [hf]

/-- Convergence is DERIVED from the finite-particle estimates. The conclusion
is local in t and does not by itself define a bounded operator on all Fock. -/
theorem local_exponential_summable {N : ℕ} (h : H) (t : ℝ) (v : D)
    (hv : ParticleBound N v.1) (ht : 2*‖h‖*((N : ℝ)+1)*|t| < 1) :
    Summable (exponentialTerm h t v) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by positivity) ht).mul_right ‖v.1‖)
  intro n
  exact exponentialTerm_norm_le h t v hv n

/-- Absolute norm summability, the analytic-vector estimate rather than
merely conditional convergence of a vector series. -/
theorem local_exponential_norm_summable {N : ℕ} (h : H) (t : ℝ) (v : D)
    (hv : ParticleBound N v.1) (ht : 2*‖h‖*((N : ℝ)+1)*|t| < 1) :
    Summable (fun n => ‖exponentialTerm h t v n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => exponentialTerm_norm_le h t v hv n)
    ((summable_geometric_of_lt_one (by positivity) ht).mul_right ‖v.1‖)

theorem bounded_particle_norm_analytic {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r → Summable (fun n => ‖exponentialTerm h t v n‖) := by
  let c : ℝ := 2*‖h‖*((N : ℝ)+1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨(c+1)⁻¹,by positivity,fun t ht => local_exponential_norm_summable h t v hv ?_⟩
  have hp : 0 < c+1 := by linarith
  have hh := (mul_lt_mul_of_pos_left ht hp)
  rw [mul_inv_cancel₀ hp.ne'] at hh
  change c*|t| < 1
  nlinarith [abs_nonneg t]

/-- Every bounded-particle vector is an analytic vector for each actual field,
with a positive radius constructed from h and its particle bound. -/
theorem bounded_particle_analytic {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r → Summable (exponentialTerm h t v) := by
  let c : ℝ := 2*‖h‖*((N : ℝ)+1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨(c+1)⁻¹,by positivity,fun t ht => local_exponential_summable h t v hv ?_⟩
  have hp : 0 < c+1 := by linarith
  have hh := (mul_lt_mul_of_pos_left ht hp)
  rw [mul_inv_cancel₀ hp.ne'] at hh
  change c*|t| < 1
  nlinarith [abs_nonneg t]

lemma ket_particleBound (m : Occ) : ParticleBound (total m) (ketD m).1 := by
  intro n hn
  have he : n ≠ m := by intro he; subst n; omega
  simp only [ketD,lp.single_apply,Pi.single_apply,he,ite_false]

/-- The occupation kets, whose span is dense, are actual analytic vectors. -/
theorem ket_analytic (h : H) (m : Occ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r → Summable (exponentialTerm h t (ketD m)) :=
  bounded_particle_analytic h (ketD m) (ket_particleBound m)

variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

lemma identity_word_particleBound (fs : List (PhysicalTensor.L2T L)) :
    ParticleBound fs.length (word (physicalBasis L) identitySource fs (ketD 0)).1 := by
  induction fs with
  | nil => simpa [word,Occupation.total] using ket_particleBound (0 : Occ)
  | cons f fs ih =>
    rw [word,sourceCre_identity]
    exact C_particleBound _ _ ih

lemma identity_polynomial_particleBound (c : List (PhysicalTensor.L2T L) →₀ ℂ) :
    ∃ N : ℕ, ParticleBound N (evalDomain (physicalBasis L) identitySource (ketD 0) c).1 := by
  induction c using Finsupp.induction_linear with
  | zero =>
    refine ⟨0,?_⟩
    intro m _
    simp
  | add c d hc hd =>
    obtain ⟨N,hN⟩ := hc
    obtain ⟨M,hM⟩ := hd
    refine ⟨max N M,?_⟩
    intro m hm
    simp only [map_add,Submodule.coe_add,lp.coeFn_add,Pi.add_apply]
    rw [hN m (lt_of_le_of_lt (le_max_left N M) hm),
      hM m (lt_of_le_of_lt (le_max_right N M) hm),zero_add]
  | single fs z =>
    refine ⟨fs.length,?_⟩
    intro m hm
    have he := identity_word_particleBound fs m hm
    simp only [evalDomain,Finsupp.linearCombination_single,Submodule.coe_smul,
      lp.coeFn_smul,Pi.smul_apply,he,smul_zero]

/-- The entire dense identity polynomial core consists of actual analytic
vectors, including arbitrary infinite-support one-particle creator smearings. -/
theorem polynomial_analytic (h : H) (c : List (PhysicalTensor.L2T L) →₀ ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
      Summable (exponentialTerm h t (evalDomain (physicalBasis L) identitySource (ketD 0) c)) := by
  obtain ⟨N,hN⟩ := identity_polynomial_particleBound c
  exact bounded_particle_analytic h _ hN

/-- Absolute analytic-vector summability on every actual polynomial vector. -/
theorem polynomial_norm_analytic (h : H) (c : List (PhysicalTensor.L2T L) →₀ ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r →
      Summable (fun n => ‖exponentialTerm h t
        (evalDomain (physicalBasis L) identitySource (ketD 0) c) n‖) := by
  obtain ⟨N,hN⟩ := identity_polynomial_particleBound c
  exact bounded_particle_norm_analytic h _ hN

end QuantumNLS.Ext006AnalyticFieldR42a
#print axioms QuantumNLS.Ext006AnalyticFieldR42a.field_power_norm_le
#print axioms QuantumNLS.Ext006AnalyticFieldR42a.local_exponential_summable
#print axioms QuantumNLS.Ext006AnalyticFieldR42a.ket_analytic
#print axioms QuantumNLS.Ext006AnalyticFieldR42a.polynomial_analytic
#print axioms QuantumNLS.Ext006AnalyticFieldR42a.polynomial_norm_analytic

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006AnalyticFieldR42a." then
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

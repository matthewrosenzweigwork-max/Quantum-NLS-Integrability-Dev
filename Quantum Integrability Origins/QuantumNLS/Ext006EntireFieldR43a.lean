import QuantumNLS.Ext006AnalyticFieldR42a

/-! Entire convergence of the ACTUAL field exponential on bounded-particle
vectors. The square-root factorial estimate is retained. No bounded Weyl
operator, spectral theorem or self-adjointness conclusion is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.Ext006EntireFieldR43a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006AnalyticFieldR42a

/-- Squared scalar majorant before taking its square root. -/
def squareMajorant (N : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  c^n * ((N+n).factorial : ℝ) / (n.factorial : ℝ)^2

lemma squareMajorant_nonneg (N : ℕ) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ squareMajorant N c n := by unfold squareMajorant; positivity

lemma squareMajorant_step (N : ℕ) (c : ℝ) (n : ℕ) :
    squareMajorant N c (n+1) * ((n : ℝ)+1)^2 =
      c * ((N : ℝ)+(n : ℝ)+1) * squareMajorant N c n := by
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  simp only [squareMajorant, Nat.add_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_succ, Nat.cast_add, pow_succ]
  field_simp

/-- The square roots are summable at EVERY finite parameter. This is a
ratio estimate proved from factorials, with no analytic-vector theorem used. -/
theorem summable_sqrt_majorant (N : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    Summable (fun n => Real.sqrt (squareMajorant N c n)) := by
  obtain ⟨K,hK⟩ := exists_nat_gt (4*c*((N : ℝ)+1))
  apply summable_of_ratio_norm_eventually_le (r := (1/2 : ℝ)) (by norm_num)
  filter_upwards [eventually_atTop.2 ⟨K,fun n hn => hn⟩] with n hn
  have hnc : 4*c*((N : ℝ)+1) ≤ (n : ℝ)+1 := by
    have hkn : (K : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hfac : (N : ℝ)+(n : ℝ)+1 ≤ ((N : ℝ)+1)*((n : ℝ)+1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N,Nat.cast_nonneg (α := ℝ) n]
  have hscalar : c*((N : ℝ)+(n : ℝ)+1) ≤ (1/4 : ℝ)*((n : ℝ)+1)^2 := by
    have h1 := mul_le_mul_of_nonneg_left hfac hc
    have h2 := mul_le_mul_of_nonneg_right hnc (show 0 ≤ (n : ℝ)+1 by positivity)
    nlinarith
  have hq := squareMajorant_step N c n
  have hbound : squareMajorant N c (n+1) ≤ (1/4 : ℝ)*squareMajorant N c n := by
    have hh := mul_le_mul_of_nonneg_right hscalar (squareMajorant_nonneg N hc n)
    have hp : 0 < ((n : ℝ)+1)^2 := by positivity
    nlinarith
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsq1 := Real.sq_sqrt (squareMajorant_nonneg N hc (n+1))
  have hsq0 := Real.sq_sqrt (squareMajorant_nonneg N hc n)
  nlinarith [Real.sqrt_nonneg (squareMajorant N c (n+1)),
    Real.sqrt_nonneg (squareMajorant N c n)]

lemma exponentialTerm_norm_sq_le {N : ℕ} (h : H) (t : ℝ) (v : D)
    (hv : ParticleBound N v.1) (n : ℕ) :
    ‖exponentialTerm h t v n‖^2 ≤
      squareMajorant N (4*‖h‖^2*|t|^2) n * ‖v.1‖^2 := by
  have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hN : (1 : ℝ) ≤ (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hb := field_power_norm_sq_le h v hv n
  have hh : ‖(((field h)^n) v).1‖^2 ≤
      (4*‖h‖^2)^n*((N+n).factorial : ℝ)*‖v.1‖^2 := by
    have hnon : 0 ≤ (4*‖h‖^2)^n*((N+n).factorial : ℝ)*‖v.1‖^2 := by positivity
    calc
      _ ≤ ((4*‖h‖^2)^n*((N+n).factorial : ℝ)*‖v.1‖^2) / (N.factorial : ℝ) := by
        simpa only [div_mul_eq_mul_div] using hb
      _ ≤ _ := div_le_self hnon hN
  have he : ‖exponentialTerm h t v n‖^2 =
      (|t|^n/(n.factorial : ℝ))^2 * ‖(((field h)^n) v).1‖^2 := by
    simp only [exponentialTerm,norm_smul,norm_div,norm_pow,norm_mul,
      Complex.norm_I,one_pow,one_mul,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_natCast,mul_pow]
  rw [he]
  calc
    _ ≤ (|t|^n/(n.factorial : ℝ))^2 *
        ((4*‖h‖^2)^n*((N+n).factorial : ℝ)*‖v.1‖^2) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = _ := by simp only [squareMajorant,mul_pow,div_pow]; ring

/-- Every bounded-particle smooth vector is ENTIRE for each actual smeared
field. In particular the former polynomial-dependent local radius is removed. -/
theorem entire_norm_summable {N : ℕ} (h : H) (t : ℝ) (v : D)
    (hv : ParticleBound N v.1) : Summable (fun n => ‖exponentialTerm h t v n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun n => Real.sqrt (squareMajorant N (4*‖h‖^2*|t|^2) n) * ‖v.1‖)
  · intro n
    have hb := exponentialTerm_norm_sq_le h t v hv n
    have he := Real.sq_sqrt (squareMajorant_nonneg N (show 0 ≤ 4*‖h‖^2*|t|^2 by positivity) n)
    have hn : 0 ≤ Real.sqrt (squareMajorant N (4*‖h‖^2*|t|^2) n) * ‖v.1‖ := by positivity
    nlinarith [norm_nonneg (exponentialTerm h t v n)]
  · exact (summable_sqrt_majorant N (by positivity)).mul_right ‖v.1‖

theorem entire_summable {N : ℕ} (h : H) (t : ℝ) (v : D)
    (hv : ParticleBound N v.1) : Summable (exponentialTerm h t v) :=
  (entire_norm_summable h t v hv).of_norm

end QuantumNLS.Ext006EntireFieldR43a
#print axioms QuantumNLS.Ext006EntireFieldR43a.entire_norm_summable
#print axioms QuantumNLS.Ext006EntireFieldR43a.entire_summable

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006EntireFieldR43a." then
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
  Lean.logInfo m!"Round43a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."

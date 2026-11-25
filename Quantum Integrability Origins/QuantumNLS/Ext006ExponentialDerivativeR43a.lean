import QuantumNLS.Ext006ExponentialContinuityR43a
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Differentiation of the literal whole-space exponential on its actual
finite-particle core. No generator or self-adjointness premise is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.Ext006ExponentialDerivativeR43a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006AnalyticFieldR42a
open Ext006EntireFieldR43a Ext006ExponentialInnerR43a Ext006BoundedExponentialR43a
open Ext006SeriesIdentificationR43a Ext006ExponentialContinuityR43a

def derivativeTerm (h : H) (t : ℝ) (v : D) : ℕ → Fock
  | 0 => 0
  | n+1 => Complex.I • exponentialTerm h t (field h v) n

lemma term_hasDerivAt (h : H) (v : D) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exponentialTerm h s v n) (derivativeTerm h t v n) t := by
  cases n with
  | zero => simpa only [exponentialTerm,pow_zero,Nat.factorial_zero,Nat.cast_one,
      div_one,one_smul,Module.End.one_apply,derivativeTerm] using hasDerivAt_const t v.1
  | succ n =>
    have hd := (((((hasDerivAt_id t).ofReal_comp).const_mul Complex.I).pow (n+1)).div_const
      ((n+1).factorial : ℂ)).smul_const ((((field h)^(n+1)) v).1)
    convert hd using 1
    · rfl
    · simp only [derivativeTerm,exponentialTerm,Nat.factorial_succ,
        Nat.cast_mul,Nat.cast_add,Nat.cast_one,id_eq,Nat.add_sub_cancel,Complex.ofReal_one,mul_one]
      rw [pow_succ (field h) n]
      simp only [Module.End.mul_apply,smul_smul]
      congr 1
      have hn : ((n : ℂ)+1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      field_simp [hn,hf]

/-- Termwise differentiation is justified by a summable UNIFORM derivative
bound on a real interval around t. -/
theorem exponential_hasDerivAt {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exponential h s v)
      (Complex.I • exponential h t (field h v)) t := by
  let R : ℝ := |t|+1
  let b : ℕ → ℝ := fun n => Real.sqrt (squareMajorant (N+1) (4*‖h‖^2*R^2) n)*‖(field h v).1‖
  let u : ℕ → ℝ := fun n => if n=0 then 0 else b (n-1)
  have hb : Summable b := (summable_sqrt_majorant (N+1) (by positivity)).mul_right _
  have hu : Summable u := by
    rw [← summable_nat_add_iff 1]
    simpa only [u,Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceIte,Nat.add_sub_cancel] using hb
  have ht : t ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [le_abs_self t,neg_abs_le t]
  have hbound : ∀ n s, s ∈ Set.Ioo (-R) R → ‖derivativeTerm h s v n‖ ≤ u n := by
    intro n s hs
    cases n with
    | zero => simp only [derivativeTerm,norm_zero,u,↓reduceIte,le_refl]
    | succ n =>
      simp only [derivativeTerm,norm_smul,Complex.norm_I,one_mul,u,Nat.succ_ne_zero,
        ↓reduceIte,Nat.succ_sub_one]
      apply term_uniform_bound h R (field h v) (field_particleBound h v hv)
      exact abs_le.mpr ⟨le_of_lt hs.1,le_of_lt hs.2⟩
  have hd := hasDerivAt_tsum_of_isPreconnected (g := fun n s => exponentialTerm h s v n)
    (g' := fun n s => derivativeTerm h s v n) hu isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    (fun n s _ => term_hasDerivAt h v n s) hbound ht (entire_summable h t v hv) ht
  apply hd.congr_deriv
  have hs := entire_summable h t (field h v) (field_particleBound h v hv)
  have hds : Summable (derivativeTerm h t v) := by
    rw [← summable_nat_add_iff 1]
    exact hs.const_smul Complex.I
  have he := hds.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,derivativeTerm,zero_add] at he
  exact he.symm.trans (hs.tsum_const_smul Complex.I)

/-- The constructed bounded group has the actual field as its strong
infinitesimal action on every bounded-particle smooth vector. -/
theorem unitary_hasDerivAt {N : ℕ} (h : H) (v : D) (hv : ParticleBound N v.1) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitary h s v.1)
      (Complex.I • unitary h t (field h v).1) t := by
  have he : (fun s : ℝ => unitary h s v.1) = (fun s : ℝ => exponential h s v) :=
    funext (fun s => unitary_series h s v (entire_summable h s v hv))
  rw [he,unitary_series h t (field h v)
    (entire_summable h t (field h v) (field_particleBound h v hv))]
  exact exponential_hasDerivAt h v hv t

end QuantumNLS.Ext006ExponentialDerivativeR43a
#print axioms QuantumNLS.Ext006ExponentialDerivativeR43a.exponential_hasDerivAt
#print axioms QuantumNLS.Ext006ExponentialDerivativeR43a.unitary_hasDerivAt

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ExponentialDerivativeR43a." then
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

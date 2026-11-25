import QuantumNLS.Ext006ExponentialGraphR43a
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Vanishing deficiency spaces for the actual smeared field on the
bounded-particle analytic core, proved from the literal entire series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006FieldDeficiencyR44a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006BoundedExponentialR43a
open Ext006EntireFieldR43a Ext006AnalyticFieldR42a Ext006ExponentialInnerR43a
open Ext006SeriesIdentificationR43a

/-- A nonreal eigenvector of the adjoint tested on the actual entire core. -/
def Defect (h : H) (a : ℝ) (z : Fock) : Prop :=
  ∀ v : Core, inner ℂ (field h v.1).1 z =
    (Complex.I*(a : ℂ))*inner ℂ (inclusion v) z

lemma defect_power (h : H) (a : ℝ) (z : Fock) (hz : Defect h a z)
    (v : Core) (n : ℕ) :
    inner ℂ (((field h)^n) v.1).1 z =
      (Complex.I*(a : ℂ))^n*inner ℂ (inclusion v) z := by
  obtain ⟨N,hN⟩ := v.2
  induction n with
  | zero => simp [inclusion]
  | succ n ih =>
    rw [pow_succ',Module.End.mul_apply]
    have he := hz ⟨((field h)^n) v.1,⟨N+n,field_power_particleBound h v.1 hN n⟩⟩
    change inner ℂ (field h (((field h)^n) v.1)).1 z =
      (Complex.I*(a : ℂ))*inner ℂ (((field h)^n) v.1).1 z at he
    rw [he,ih,pow_succ']
    ring

/-- An imaginary adjoint eigenvalue would produce exponential growth of
matrix elements of an actual unitary group. -/
theorem defect_exponential (h : H) (a : ℝ) (z : Fock) (hz : Defect h a z)
    (v : Core) (t : ℝ) :
    inner ℂ (unitary h t (inclusion v)) z =
      (Real.exp (t*a) : ℂ)*inner ℂ (inclusion v) z := by
  obtain ⟨N,hN⟩ := v.2
  have hs := (innerSLFlip ℂ z).hasSum (entire_summable h t v.1 hN).hasSum
  have he := (NormedSpace.expSeries_div_hasSum_exp ((t*a : ℝ) : ℂ)).mul_right
    (inner ℂ (inclusion v) z)
  rw [← Complex.exp_eq_exp_ℂ,← Complex.ofReal_exp] at he
  have hterm (n : ℕ) : inner ℂ (exponentialTerm h t v.1 n) z =
      ((t*a : ℝ) : ℂ)^n/(n.factorial : ℂ)*inner ℂ (inclusion v) z := by
    rw [exponentialTerm,inner_smul_left,defect_power h a z hz v n]
    simp only [map_div₀,map_pow,map_mul,
      Complex.conj_I,Complex.conj_ofReal,map_natCast,Complex.ofReal_mul]
    have hb : (-Complex.I*(t : ℂ))*(Complex.I*(a : ℂ))=(t : ℂ)*(a : ℂ) := by
      ring_nf
      simp [Complex.I_sq]
    calc
      _ = (((-Complex.I*(t : ℂ))*(Complex.I*(a : ℂ)))^n/(n.factorial : ℂ))*
          inner ℂ (inclusion v) z := by rw [mul_pow]; ring
      _ = _ := by rw [hb]
  change HasSum (fun n => inner ℂ (exponentialTerm h t v.1 n) z)
    (inner ℂ (exponential h t v.1) z) at hs
  simp only [hterm] at hs
  rw [unitary_core,exponential]
  exact hs.unique he

/-- Both deficiency spaces vanish; in fact every nonzero purely imaginary
adjoint eigenvalue has trivial eigenspace. The operator closure and Stone
identification still require their explicit graph argument. -/
theorem defect_zero (h : H) (a : ℝ) (ha : a ≠ 0) (z : Fock)
    (hz : Defect h a z) : z = 0 := by
  have hcore (v : Core) : inner ℂ (inclusion v) z = 0 := by
    by_contra hn
    let d : ℝ := ‖inner ℂ (inclusion v) z‖
    let C : ℝ := ‖inclusion v‖*‖z‖
    have hd : 0 < d := norm_pos_iff.mpr hn
    let t : ℝ := (C/d+1)/a
    have ht : t*a = C/d+1 := div_mul_cancel₀ _ ha
    have hb := norm_inner_le_norm (𝕜 := ℂ) (unitary h t (inclusion v)) z
    rw [defect_exponential h a z hz v t,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),LinearIsometryEquiv.norm_map] at hb
    change Real.exp (t*a)*d ≤ C at hb
    have he := Real.add_one_le_exp (C/d+1)
    rw [ht] at hb
    have hdC : C/d*d=C := div_mul_cancel₀ _ hd.ne'
    nlinarith
  apply ext_inner_left ℂ
  intro x
  rw [inner_zero_right]
  exact core_dense.induction_on (p := fun x => inner ℂ x z=0) x
    (isClosed_eq (continuous_id.inner continuous_const) continuous_const) hcore

end QuantumNLS.Ext006FieldDeficiencyR44a
#print axioms QuantumNLS.Ext006FieldDeficiencyR44a.defect_exponential
#print axioms QuantumNLS.Ext006FieldDeficiencyR44a.defect_zero

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006FieldDeficiencyR44a." then
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
  Lean.logInfo m!"Round44a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."

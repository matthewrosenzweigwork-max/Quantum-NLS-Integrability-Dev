import QuantumNLS.Ext006BoundedExponentialR43a

/-! Identification of the bounded unitary with every convergent ACTUAL
field series, including non-finite-particle vectors, and its global time
group law. This still does not assert a self-adjoint closure theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SeriesIdentificationR43a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006AnalyticFieldR42a
open Ext006EntireFieldR43a Ext006ExponentialInnerR43a Ext006BoundedExponentialR43a

lemma term_adjoint (h : H) (t : ℝ) (v w : D) (n : ℕ) :
    inner ℂ (exponentialTerm h (-t) v n) w.1 =
      inner ℂ v.1 (exponentialTerm h t w n) := by
  have he := inner_terms h (-t) 0 v w n 0
  simpa only [coeff,exponentialTerm,pow_zero,Nat.factorial_zero,Nat.cast_one,
    div_one,one_smul,Module.End.one_apply,mul_one,Nat.add_zero,
    Complex.ofReal_neg,mul_neg,neg_mul,neg_neg,inner_smul_right] using he

lemma exponential_adjoint (h : H) (t : ℝ) (v w : D)
    (hv : Summable (exponentialTerm h (-t) v)) (hw : Summable (exponentialTerm h t w)) :
    inner ℂ (exponential h (-t) v) w.1 = inner ℂ v.1 (exponential h t w) := by
  unfold exponential
  calc
    _ = ∑' n, inner ℂ (exponentialTerm h (-t) v n) w.1 := (innerSLFlip ℂ w.1).map_tsum hv
    _ = ∑' n, inner ℂ v.1 (exponentialTerm h t w n) := tsum_congr (term_adjoint h t v w)
    _ = _ := ((innerSL ℂ v.1).map_tsum hw).symm

/-- Identification holds on any smooth vector for which this literal series
converges, including the constructed squeezed source polynomial domain. -/
theorem unitary_series (h : H) (t : ℝ) (v : D)
    (hv : Summable (exponentialTerm h t v)) :
    unitary h t v.1 = exponential h t v := by
  apply ext_inner_left ℂ
  intro x
  refine core_dense.induction_on
    (p := fun x => inner ℂ x (unitary h t v.1) = inner ℂ x (exponential h t v)) x
    (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)) ?_
  intro w
  obtain ⟨M,hM⟩ := w.2
  change inner ℂ (inclusion w) (evolution h t v.1) = _
  rw [evolution_adjoint,evolution_core]
  simpa only [inclusion,LinearMap.comp_apply,Submodule.subtype_apply] using
    exponential_adjoint h t w.1 v (entire_summable h (-t) w.1 hM) hv

/-- The mixed inner-product identity extends to arbitrary Fock vectors. -/
theorem unitary_inner_shift (h : H) (s t : ℝ) (x y : Fock) :
    inner ℂ (unitary h s x) (unitary h t y) = inner ℂ x (unitary h (t-s) y) := by
  apply core_dense.induction_on₂
    (p := fun x y => inner ℂ (unitary h s x) (unitary h t y) =
      inner ℂ x (unitary h (t-s) y))
    (isClosed_eq (((unitary h s).continuous.comp continuous_fst).inner
        ((unitary h t).continuous.comp continuous_snd))
      (continuous_fst.inner ((unitary h (t-s)).continuous.comp continuous_snd))) ?_ x y
  intro v w
  obtain ⟨N,hN⟩ := v.2
  obtain ⟨M,hM⟩ := w.2
  rw [unitary_core,unitary_core,unitary_core]
  simpa only [inclusion,LinearMap.comp_apply,Submodule.subtype_apply] using
    inner_exponentials h s t v.1 w.1 hN hM

/-- A genuine one-parameter unitary group is constructed, rather than assumed. -/
theorem unitary_add (h : H) (s t : ℝ) (x : Fock) :
    unitary h s (unitary h t x) = unitary h (s+t) x := by
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y (evolution h s (unitary h t x)) = _
  rw [evolution_adjoint]
  change inner ℂ (unitary h (-s) y) (unitary h t x) = _
  rw [unitary_inner_shift]
  rw [show t-(-s)=s+t by ring]

theorem unitary_zero (h : H) (x : Fock) : unitary h 0 x = x := by
  refine core_dense.induction_on (p := fun x => unitary h 0 x=x) x
    (isClosed_eq (unitary h 0).continuous continuous_id) ?_
  intro v
  rw [unitary_core,exponential_zero]
  rfl

end QuantumNLS.Ext006SeriesIdentificationR43a
#print axioms QuantumNLS.Ext006SeriesIdentificationR43a.unitary_series
#print axioms QuantumNLS.Ext006SeriesIdentificationR43a.unitary_add

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SeriesIdentificationR43a." then
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

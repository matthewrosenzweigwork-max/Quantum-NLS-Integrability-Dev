import QuantumNLS.Ext005WeakTestsR36b
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Integral convergence for arbitrary subfilters from uniform convergence
on a finite interval. No countably-generated-filter assumption is used.
This is the scalar integration bridge needed after R36b weak uniformity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Topology
open Set Filter MeasureTheory
namespace QuantumNLS.Ext005NetIntegralR36b

/-- Uniform scalar convergence on a finite interval passes through the
integral along ANY filter. This does not misuse sequential dominated
convergence for the compactness subfilter. -/
theorem integral_tendsto_of_uniform_on (a b : ℝ)
    (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (L : Filter ℕ)
    (hF : ∀ n, IntegrableOn (F n) (Icc a b))
    (hf : IntegrableOn f (Icc a b))
    (hu : TendstoUniformlyOn F f L (Icc a b)) :
    Tendsto (fun n => ∫ t in Icc a b, F n t) L (𝓝 (∫ t in Icc a b, f t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let μ := volume.restrict (Icc a b)
  let r := μ.real Set.univ
  have hr : 0 ≤ r := measureReal_nonneg
  have hd : 0 < r+1 := by linarith
  let δ := ε / (r+1)
  have hδ : 0 < δ := div_pos hε hd
  have heq : δ * (r+1) = ε := div_mul_cancel₀ ε hd.ne'
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu δ hδ] with n hn
  rw [dist_eq_norm, ← integral_sub (hF n) hf]
  have hbound : ‖∫ t, F n t - f t ∂μ‖ ≤ δ * r := by
    apply norm_integral_le_of_norm_le_const
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht
    simpa only [dist_eq_norm, norm_sub_rev] using (hn t ht).le
  exact hbound.trans_lt (by nlinarith)

/-- The same arbitrary-filter result for globally written test integrals
whose integrands vanish outside the finite interval. -/
theorem global_integral_tendsto_of_uniform_on (a b : ℝ)
    (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (L : Filter ℕ)
    (hF : ∀ n, IntegrableOn (F n) (Icc a b))
    (hf : IntegrableOn f (Icc a b))
    (hF0 : ∀ n t, t ∉ Icc a b → F n t = 0)
    (hf0 : ∀ t, t ∉ Icc a b → f t = 0)
    (hu : TendstoUniformlyOn F f L (Icc a b)) :
    Tendsto (fun n => ∫ t, F n t) L (𝓝 (∫ t, f t)) := by
  have heq (n : ℕ) : (∫ t in Icc a b, F n t) = ∫ t, F n t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hF0 n)
  have heqf : (∫ t in Icc a b, f t) = ∫ t, f t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hf0
  simpa only [heq, heqf] using integral_tendsto_of_uniform_on a b F f L hF hf hu

end QuantumNLS.Ext005NetIntegralR36b
#print axioms QuantumNLS.Ext005NetIntegralR36b.global_integral_tendsto_of_uniform_on

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005NetIntegralR36b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005NetIntegralR36b." then
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
  Lean.logInfo m!"R36b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

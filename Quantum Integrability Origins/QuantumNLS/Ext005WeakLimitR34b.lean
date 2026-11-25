import QuantumNLS.Ext005WeakConsistencyR34b
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Passage to a bounded weak limit in the distributional equation.
This proves weak-equation closure, not extraction or continuity of a limit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005WeakLimitR34b
open Ext005IntervalChainR111
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/-- Dominated convergence for compactly supported scalar tests of bounded
weakly convergent Hilbert-valued functions. No limit equation is a premise. -/
theorem paired_integral_tendsto (a b : ℝ) (F : ℕ → ℝ → Q) (f : ℝ → Q) (M : ℝ)
    (hm : ∀ n, AEStronglyMeasurable (F n))
    (hb : ∀ n t, t ∈ Icc a b → ‖F n t‖ ≤ M)
    (hw : ∀ t ∈ Icc a b, ∀ v : Q,
      Tendsto (fun n => ⟪v, F n t⟫_ℝ) atTop (𝓝 ⟪v, f t⟫_ℝ))
    (v : Q) (p : ℝ → ℝ) (hp : Continuous p) (hc : HasCompactSupport p)
    (hs : tsupport p ⊆ Icc a b) :
    Tendsto (fun n => ∫ t, p t * ⟪v, F n t⟫_ℝ) atTop
      (𝓝 (∫ t, p t * ⟪v, f t⟫_ℝ)) := by
  apply tendsto_integral_of_dominated_convergence (fun t => ‖p t‖ * (‖v‖ * M))
  · intro n
    exact hp.aestronglyMeasurable.mul (aestronglyMeasurable_const.inner (hm n))
  · exact ((hp.integrable_of_hasCompactSupport hc).norm).mul_const _
  · intro n
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ Icc a b
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hb n t ht) (norm_nonneg _)))
        (norm_nonneg _)
    · have hz : p t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hs h))
      simp only [hz, zero_mul, norm_zero, le_refl]
  · apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ Icc a b
    · exact (hw t ht v).const_mul (p t)
    · have hz : p t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hs h))
      simpa only [hz, zero_mul] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Every uniformly bounded pointwise weak limit of the approximate
weak equations satisfies the original distributional equation. Strong
convergence of the evolving vectors is not needed. -/
theorem weak_derivative_limit (a b : ℝ) (F G : ℕ → ℝ → Q) (f g : ℝ → Q)
    (M N : ℝ) (hfm : ∀ n, AEStronglyMeasurable (F n))
    (hgm : ∀ n, AEStronglyMeasurable (G n))
    (hfb : ∀ n t, t ∈ Icc a b → ‖F n t‖ ≤ M)
    (hgb : ∀ n t, t ∈ Icc a b → ‖G n t‖ ≤ N)
    (hfc : ∀ t ∈ Icc a b, ∀ v : Q,
      Tendsto (fun n => ⟪v, F n t⟫_ℝ) atTop (𝓝 ⟪v, f t⟫_ℝ))
    (hgc : ∀ t ∈ Icc a b, ∀ v : Q,
      Tendsto (fun n => ⟪v, G n t⟫_ℝ) atTop (𝓝 ⟪v, g t⟫_ℝ))
    (heq : ∀ n, WeakDerivativeOn (Ioo a b) (F n) (G n)) :
    WeakDerivativeOn (Ioo a b) f g := by
  intro v p hp hc hs
  have hs' : tsupport p ⊆ Icc a b := hs.trans Ioo_subset_Icc_self
  have hl := paired_integral_tendsto a b F f M hfm hfb hfc v (deriv p)
    (hp.continuous_deriv (by exact_mod_cast le_top)) hc.deriv
    (tsupport_deriv_subset.trans hs')
  have hr := (paired_integral_tendsto a b G g N hgm hgb hgc v p hp.continuous hc hs').neg
  have hn : (fun n => ∫ t, deriv p t * ⟪v, F n t⟫_ℝ) =
      (fun n => -(∫ t, p t * ⟪v, G n t⟫_ℝ)) := funext fun n => heq n v p hp hc hs
  rw [hn] at hl
  exact tendsto_nhds_unique hl hr

end QuantumNLS.Ext005WeakLimitR34b
#print axioms QuantumNLS.Ext005WeakLimitR34b.paired_integral_tendsto
#print axioms QuantumNLS.Ext005WeakLimitR34b.weak_derivative_limit

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005WeakLimitR34b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005WeakLimitR34b." then
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
  Lean.logInfo m!"R34b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

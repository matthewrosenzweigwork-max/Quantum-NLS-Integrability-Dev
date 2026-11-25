import QuantumNLS.Ext005NetIntegralR36b
import QuantumNLS.Ext005NetForceR36b
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Net-compatible distributional closure, with the classical integration by
parts step proved on the actual finite interval. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory Function
namespace QuantumNLS.Ext005WeakEquationR37b
open Ext005IntervalChainR111 Ext005NetIntegralR36b

/-- Bounded continuous scalar tests preserve uniform convergence along an
arbitrary filter on a compact interval. -/
lemma uniform_mul (a b : ℝ) (F : ℕ → ℝ → ℝ) (f p : ℝ → ℝ)
    (L : Filter ℕ) (hp : ContinuousOn p (Icc a b))
    (h : TendstoUniformlyOn F f L (Icc a b)) :
    TendstoUniformlyOn (fun n t => p t * F n t) (fun t => p t * f t) L (Icc a b) := by
  obtain ⟨R, hR, hb⟩ := (isCompact_Icc.image_of_continuousOn hp).isBounded.exists_pos_norm_le
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hd : 0 < ε / R := div_pos hε hR
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h (ε/R) hd] with n hn t ht
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  calc
    _ ≤ R * ‖f t - F n t‖ := mul_le_mul_of_nonneg_right (hb _ ⟨t, ht, rfl⟩) (norm_nonneg _)
    _ < R * (ε/R) := mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hn t ht) hR
    _ = ε := mul_div_cancel₀ ε hR.ne'

/-- Continuous compact tests pass through scalar uniform limits along any
filter. The limit's integrability is derived from scalar continuity. -/
theorem tested_integral_tendsto (a b : ℝ) (F : ℕ → ℝ → ℝ) (f p : ℝ → ℝ)
    (L : Filter ℕ) [NeBot L] (hF : ∀ n, ContinuousOn (F n) (Icc a b))
    (hu : TendstoUniformlyOn F f L (Icc a b))
    (hp : Continuous p) (hs : tsupport p ⊆ Icc a b) :
    Tendsto (fun n => ∫ t, p t * F n t) L (𝓝 (∫ t, p t * f t)) := by
  have hf := hu.continuousOn (Eventually.of_forall hF).frequently
  apply global_integral_tendsto_of_uniform_on a b
  · intro n
    exact (hp.continuousOn.mul (hF n)).integrableOn_compact isCompact_Icc
  · exact (hp.continuousOn.mul hf).integrableOn_compact isCompact_Icc
  · intro n t ht
    rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hs h)), zero_mul]
  · intro t ht
    rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hs h)), zero_mul]
  · exact uniform_mul a b F f p L hp.continuousOn hu

variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/-- A classical curve with continuous derivative on the finite interval
satisfies exactly the inherited distributional equation there. -/
theorem classical_weak (a b : ℝ) (hab : a ≤ b) (f g : ℝ → Q)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (g t) t) :
    WeakDerivativeOn (Ioo a b) f g := by
  intro v p hp hc hs
  have hp' : Continuous (deriv p) := hp.continuous_deriv (by exact_mod_cast le_top)
  have hu : ContinuousOn (fun t => ⟪v, f t⟫_ℝ) (uIcc a b) := by
    simpa only [uIcc_of_le hab] using continuousOn_const.inner hf
  have hv : ContinuousOn p (uIcc a b) := hp.continuous.continuousOn
  have hgc : ContinuousOn (fun t => ⟪v, g t⟫_ℝ) (uIcc a b) := by
    simpa only [uIcc_of_le hab] using continuousOn_const.inner hg
  have hgu : IntervalIntegrable (fun t => ⟪v, g t⟫_ℝ) volume a b :=
    hgc.intervalIntegrable
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hv
    (fun t ht => (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt t
      (hd t (by simpa only [min_eq_left hab, max_eq_right hab] using Ioo_subset_Icc_self ht)))
    (fun t _ => (hp.differentiable (by simp)).differentiableAt.hasDerivAt)
    hgu (hp'.intervalIntegrable a b)
  have he (t : ℝ) (ht : t = a ∨ t = b) : p t = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hh := hs h
    rcases ht with rfl | rfl <;> linarith [hh.1, hh.2]
  rw [he b (Or.inr rfl), he a (Or.inl rfl), mul_zero, mul_zero, sub_zero, zero_sub] at h
  have hl : (∫ t in a..b, ⟪v, f t⟫_ℝ * deriv p t) = ∫ t, deriv p t * ⟪v, f t⟫_ℝ := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset
      ((support_mul_subset_right _ _).trans (fun t ht => Ioo_subset_Ioc_self (hs (tsupport_deriv_subset (subset_closure ht)))))]
    simp only [mul_comm]
  have hr : (∫ t in a..b, ⟪v, g t⟫_ℝ * p t) = ∫ t, p t * ⟪v, g t⟫_ℝ := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset
      ((support_mul_subset_right _ _).trans (fun t ht => Ioo_subset_Ioc_self (hs (subset_closure ht))))]
    simp only [mul_comm]
  simp only [innerSL_apply_apply] at h
  rw [hl, hr] at h
  exact h

/-- Uniform scalar closure of the weak equation along a nontrivial NET;
no countable-generation or sequential dominated-convergence premise. -/
theorem weak_limit (a b : ℝ) (F G : ℕ → ℝ → Q) (f g : ℝ → Q)
    (L : Filter ℕ) [NeBot L]
    (hF : ∀ n, ContinuousOn (F n) (Icc a b))
    (hG : ∀ n, ContinuousOn (G n) (Icc a b))
    (hu : ∀ v : Q, TendstoUniformlyOn (fun n t => ⟪v, F n t⟫_ℝ)
      (fun t => ⟪v, f t⟫_ℝ) L (Icc a b))
    (hv : ∀ v : Q, TendstoUniformlyOn (fun n t => ⟪v, G n t⟫_ℝ)
      (fun t => ⟪v, g t⟫_ℝ) L (Icc a b))
    (he : ∀ n, WeakDerivativeOn (Ioo a b) (F n) (G n)) :
    WeakDerivativeOn (Ioo a b) f g := by
  intro v p hp hc hs
  have hl := tested_integral_tendsto a b _ _ (deriv p) L
    (fun n => continuousOn_const.inner (hF n)) (hu v)
    (hp.continuous_deriv (by exact_mod_cast le_top))
    (tsupport_deriv_subset.trans (hs.trans Ioo_subset_Icc_self))
  have hr := (tested_integral_tendsto a b _ _ p L
    (fun n => continuousOn_const.inner (hG n)) (hv v) hp.continuous
    (hs.trans Ioo_subset_Icc_self)).neg
  have hn : (fun n => ∫ t, deriv p t * ⟪v, F n t⟫_ℝ) =
      (fun n => -(∫ t, p t * ⟪v, G n t⟫_ℝ)) := funext fun n => he n v p hp hc hs
  rw [hn] at hl
  exact tendsto_nhds_unique hl hr

end QuantumNLS.Ext005WeakEquationR37b
#print axioms QuantumNLS.Ext005WeakEquationR37b.weak_limit
#print axioms QuantumNLS.Ext005WeakEquationR37b.classical_weak

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005WeakEquationR37b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005WeakEquationR37b." then
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
  Lean.logInfo m!"R37b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

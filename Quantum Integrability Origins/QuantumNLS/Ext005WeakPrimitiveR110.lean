import QuantumNLS.Ext005WeakConstantR110
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Support

/-! R110: deriving a scalar primitive identity from the distributional weak
form with locally integrable forcing. Neither absolute continuity nor an
integral equation is a premise on the unknown curve. -/
noncomputable section
set_option autoImplicit false
open scoped Topology ContDiff
open MeasureTheory Set Filter Function
namespace QuantumNLS.Ext005WeakPrimitiveR110
open Ext005WeakConstantR110

lemma locallyIntegrable_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : LocallyIntegrable g) (a b : ℝ) :
    IntervalIntegrable g volume a b :=
  intervalIntegrable_iff.mpr
    ((hg.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

/-- Integration by parts for the actual primitive of a locally integrable
forcing, against smooth compactly supported tests. -/
theorem primitive_weak_form (g : ℝ → ℝ) (hg : LocallyIntegrable g)
    (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hc : HasCompactSupport p) :
    ∫ t, deriv p t * (∫ v in 0..t, g v) = -(∫ t, p t * g t) := by
  let P := fun t => ∫ v in 0..t, g v
  have hP : Continuous P := intervalIntegral.continuous_primitive
    (locallyIntegrable_interval hg) 0
  obtain ⟨R, hR, hb⟩ :=
    (hc.isCompact.union hc.deriv.isCompact).isBounded.exists_pos_norm_lt
  have hs {f : ℝ → ℝ} (hf : tsupport f ⊆ tsupport p ∪ tsupport (deriv p)) :
      support f ⊆ Ioc (-R) R := by
    intro t ht
    have h := hb t (hf (subset_closure ht))
    rw [Real.norm_eq_abs, abs_lt] at h
    exact ⟨h.1, h.2.le⟩
  have hsp : support p ⊆ Ioc (-R) R := hs subset_union_left
  have hsd : support (deriv p) ⊆ Ioc (-R) R := hs subset_union_right
  have hpe (t : ℝ) (ht : t = -R ∨ t = R) : p t = 0 := by
    by_contra hn
    have h := hb t (Or.inl (subset_closure hn))
    rw [Real.norm_eq_abs, abs_lt] at h
    rcases ht with rfl | rfl <;> linarith
  have hPa : AbsolutelyContinuousOnInterval P (-R) R :=
    (locallyIntegrable_interval hg (-R) R).absolutelyContinuousOnInterval_intervalIntegral
      (by rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, hR.le⟩)
  have hpa : AbsolutelyContinuousOnInterval p (-R) R :=
    (hp.of_le (by exact_mod_cast le_top)).contDiffOn.absolutelyContinuousOnInterval
  have h := hPa.integral_mul_deriv_eq_deriv_mul hpa
  rw [hpe R (Or.inr rfl), hpe (-R) (Or.inl rfl), mul_zero, mul_zero,
    sub_zero, zero_sub] at h
  have hder : (∫ t in (-R)..R, deriv P t * p t) =
      ∫ t in (-R)..R, g t * p t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg] with t ht _
    rw [(ht 0).deriv]
  rw [hder] at h
  have hl : (∫ t in (-R)..R, P t * deriv p t) = ∫ t, P t * deriv p t :=
    intervalIntegral.integral_eq_integral_of_support_subset
      ((support_mul_subset_right P (deriv p)).trans hsd)
  have hr : (∫ t in (-R)..R, g t * p t) = ∫ t, g t * p t :=
    intervalIntegral.integral_eq_integral_of_support_subset
      ((support_mul_subset_right g p).trans hsp)
  rw [hl, hr] at h
  simpa only [P, mul_comm] using h

/-- Distributional equation => integral equation for a continuous real
curve and locally integrable forcing. This implication is proved here. -/
theorem weak_to_integral (f g : ℝ → ℝ) (hf : Continuous f) (hg : LocallyIntegrable g)
    (hw : ∀ p : ℝ → ℝ, ContDiff ℝ ∞ p → HasCompactSupport p →
      ∫ t, deriv p t * f t = -(∫ t, p t * g t)) (s t : ℝ) :
    f t - f s = ∫ v in s..t, g v := by
  let P := fun t => ∫ v in 0..t, g v
  have hP : Continuous P := intervalIntegral.continuous_primitive
    (locallyIntegrable_interval hg) 0
  have hwz (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hc : HasCompactSupport p) :
      ∫ t, deriv p t • (f t - P t) = 0 := by
    have hi1 : Integrable (fun t => deriv p t • f t) volume := hf.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      (hp.continuous_deriv (by exact_mod_cast le_top)) hc.deriv
    have hi2 : Integrable (fun t => deriv p t • P t) volume := hP.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      (hp.continuous_deriv (by exact_mod_cast le_top)) hc.deriv
    simp only [smul_sub]
    rw [integral_sub hi1 hi2]
    simp only [smul_eq_mul]
    rw [hw p hp hc, primitive_weak_form g hg p hp hc, sub_self]
  have he := constant_of_weak_derivative_zero (fun t => f t - P t) (hf.sub hP) hwz s t
  have hpi : P t - P s = ∫ v in s..t, g v :=
    intervalIntegral.integral_interval_sub_left (locallyIntegrable_interval hg 0 t)
      (locallyIntegrable_interval hg 0 s)
  linarith

/-- Absolute continuity of the unknown curve is derived on each interval
from its distributional equation. -/
theorem weak_absolutelyContinuous (f g : ℝ → ℝ) (hf : Continuous f)
    (hg : LocallyIntegrable g)
    (hw : ∀ p : ℝ → ℝ, ContDiff ℝ ∞ p → HasCompactSupport p →
      ∫ t, deriv p t * f t = -(∫ t, p t * g t)) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b := by
  have ha := (locallyIntegrable_interval hg a b).absolutelyContinuousOnInterval_intervalIntegral
    (c := a) left_mem_uIcc
  have he : f = fun t => (∫ v in a..t, g v) + f a := by
    funext t
    linarith [weak_to_integral f g hf hg hw a t]
  rw [he]
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => f a)).contDiffOn.absolutelyContinuousOnInterval
  exact ha.add hc

end QuantumNLS.Ext005WeakPrimitiveR110
#print axioms QuantumNLS.Ext005WeakPrimitiveR110.primitive_weak_form
#print axioms QuantumNLS.Ext005WeakPrimitiveR110.weak_to_integral
#print axioms QuantumNLS.Ext005WeakPrimitiveR110.weak_absolutelyContinuous

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005WeakPrimitiveR110." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005WeakPrimitiveR110." then
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
  Lean.logInfo m!"R110 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! R110: the zero distributional derivative lemma. The test class is the
literal smooth, compactly supported class. Constancy is a conclusion, not
an extra weak-solution hypothesis. This module contains no energy identity. -/
noncomputable section
set_option autoImplicit false
open scoped Topology ContDiff
open MeasureTheory Set Filter Function
namespace QuantumNLS.Ext005WeakConstantR110

/-- A zero-mean smooth compactly supported function has a smooth compactly
supported primitive. The support assertion is proved from the zero integral. -/
theorem compact_primitive {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hz : ∫ t, g t = 0) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ HasCompactSupport p ∧ deriv p = g := by
  obtain ⟨R, hR, hb⟩ := hc.isCompact.isBounded.exists_pos_norm_lt
  let a := -R
  let p := fun x => ∫ t in a..x, g t
  have hd (x : ℝ) : HasDerivAt p (g x) x :=
    (hg.continuous.integral_hasStrictDerivAt a x).hasDerivAt
  have he : deriv p = g := funext fun x => (hd x).deriv
  refine ⟨p, contDiff_infty_iff_deriv.mpr ⟨fun x => (hd x).differentiableAt,
    he.symm ▸ hg⟩, ?_, he⟩
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := a) (b := R))
  intro x hx
  by_contra hn
  have hx' : p x ≠ 0 := hx
  have gz (t : ℝ) (ht : t ≤ a ∨ R ≤ t) : g t = 0 := by
    by_contra ht'
    have h := hb t (subset_closure ht')
    rw [Real.norm_eq_abs, abs_lt] at h
    dsimp [a] at ht
    rcases ht with ht | ht <;> linarith
  have hor : x < a ∨ R < x := by simpa only [mem_Icc, not_and_or, not_le] using hn
  rcases hor with hxlo | hxhi
  · apply hx'
    dsimp [p]
    rw [intervalIntegral.integral_symm]
    have hh : (∫ t in x..a, g t) = 0 := by
      rw [← intervalIntegral.integral_zero (a := x) (b := a) (E := ℝ)]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hxlo.le] at ht
      exact gz t (Or.inl ht.2)
    rw [hh, neg_zero]
  · apply hx'
    dsimp [p]
    rw [intervalIntegral.integral_eq_integral_of_support_subset, hz]
    intro t ht
    have h := hb t (subset_closure ht)
    rw [Real.norm_eq_abs, abs_lt] at h
    exact ⟨h.1, h.2.le.trans hxhi.le⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A locally Bochner integrable vector function with zero distributional
derivative is a.e. constant. No differentiability of the function is assumed. -/
theorem ae_constant_of_weak_derivative_zero (f : ℝ → E) (hf : LocallyIntegrable f)
    (hw : ∀ p : ℝ → ℝ, ContDiff ℝ ∞ p → HasCompactSupport p →
      ∫ t, deriv p t • f t = 0) :
    ∃ c : E, ∀ᵐ t, f t = c := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let ρ := b.normed volume
  have hρ : ContDiff ℝ ∞ ρ := b.contDiff_normed
  have hcρ : HasCompactSupport ρ := b.hasCompactSupport_normed
  have hiρ : ∫ t, ρ t = 1 := b.integral_normed
  let c := ∫ t, ρ t • f t
  refine ⟨c, ?_⟩
  have hdiff : ∀ᵐ t, f t - c = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.sub (locallyIntegrable_const c))
    intro g hg hcg
    let q := fun t => g t - (∫ s, g s) * ρ t
    have hq : ContDiff ℝ ∞ q := hg.sub (contDiff_const.mul hρ)
    have hcq : HasCompactSupport q := hcg.sub hcρ.mul_left
    have hzg : ∫ t, q t = 0 := by
      rw [integral_sub (hg.continuous.integrable_of_hasCompactSupport hcg)
        ((hρ.continuous.integrable_of_hasCompactSupport hcρ).const_mul _),
        integral_const_mul, hiρ, mul_one, sub_self]
    obtain ⟨p, hp, hcp, hpg⟩ := compact_primitive hq hcq hzg
    have hzero := hw p hp hcp
    rw [hpg] at hzero
    have hig := hf.integrable_smul_left_of_hasCompactSupport hg.continuous hcg
    have hir := hf.integrable_smul_left_of_hasCompactSupport hρ.continuous hcρ
    have hval : (∫ t, g t • f t) - (∫ s, g s) • c = 0 := by
      simp only [q, sub_smul, mul_smul] at hzero
      have him : Integrable (fun t => (∫ s, g s) • (ρ t • f t)) :=
        hir.smul (∫ s, g s)
      rw [integral_sub hig him, integral_smul] at hzero
      exact hzero
    change (∫ t, g t • (f t - c)) = 0
    simp only [smul_sub]
    rw [integral_sub hig ((hg.continuous.integrable_of_hasCompactSupport hcg).smul_const c),
      integral_smul_const]
    exact hval
  filter_upwards [hdiff] with t ht using sub_eq_zero.mp ht

/-- For a continuous curve the a.e. conclusion upgrades to pointwise
constancy, including every chosen initial time. -/
theorem constant_of_weak_derivative_zero (f : ℝ → E) (hf : Continuous f)
    (hw : ∀ p : ℝ → ℝ, ContDiff ℝ ∞ p → HasCompactSupport p →
      ∫ t, deriv p t • f t = 0) (s t : ℝ) : f t = f s := by
  obtain ⟨c, hc⟩ := ae_constant_of_weak_derivative_zero f hf.locallyIntegrable hw
  have he : f = fun _ => c := hf.ae_eq_iff_eq volume continuous_const |>.mp hc
  exact (congrFun he t).trans (congrFun he s).symm

end QuantumNLS.Ext005WeakConstantR110
#print axioms QuantumNLS.Ext005WeakConstantR110.compact_primitive
#print axioms QuantumNLS.Ext005WeakConstantR110.ae_constant_of_weak_derivative_zero
#print axioms QuantumNLS.Ext005WeakConstantR110.constant_of_weak_derivative_zero

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005WeakConstantR110." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005WeakConstantR110." then
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

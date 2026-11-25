import QuantumNLS.Ext005CutoffChainR110

/-! Local distributional constancy on an open finite interval. The primitive
of a zero-mean test has support inside that same interval; no extension of
the unknown weak equation beyond the interval is assumed. -/
noncomputable section
set_option autoImplicit false
open scoped Topology ContDiff InnerProductSpace
open MeasureTheory Set Filter Function
namespace QuantumNLS.Ext005IntervalPrimitiveR111
open Ext005WeakPrimitiveR110 Ext005CutoffChainR110

/-- The compact primitive can be chosen with support in the test interval. -/
theorem compact_primitive_in (a b : ℝ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ioo a b) (hz : ∫ t, g t = 0) :
    ∃ p : ℝ → ℝ, ContDiff ℝ ∞ p ∧ HasCompactSupport p ∧
      tsupport p ⊆ Ioo a b ∧ deriv p = g := by
  by_cases he : (tsupport g).Nonempty
  · obtain ⟨c, hcm, hcmin⟩ := hc.isCompact.exists_isLeast he
    obtain ⟨d, hdm, hdmax⟩ := hc.isCompact.exists_isGreatest he
    let l := (a + c) / 2
    have hlc : l < c := by dsimp [l]; linarith [(hs hcm).1]
    have hal : a < l := by dsimp [l]; linarith [(hs hcm).1]
    let p := fun x => ∫ t in l..x, g t
    have hd (x : ℝ) : HasDerivAt p (g x) x :=
      (hg.continuous.integral_hasStrictDerivAt l x).hasDerivAt
    have hder : deriv p = g := funext fun x => (hd x).deriv
    have hsub : support p ⊆ Icc l d := by
      intro x hx
      by_contra hn
      have hx' : p x ≠ 0 := hx
      rcases (by simpa only [mem_Icc, not_and_or, not_le] using hn : x < l ∨ d < x) with hxlo | hxhi
      · apply hx'
        dsimp [p]
        rw [intervalIntegral.integral_symm]
        have hh : (∫ t in x..l, g t) = 0 := by
          rw [← intervalIntegral.integral_zero (a := x) (b := l) (E := ℝ)]
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hxlo.le] at ht
          by_contra hgz
          have := hcmin (subset_closure hgz)
          linarith [ht.2]
        rw [hh, neg_zero]
      · apply hx'
        dsimp [p]
        rw [intervalIntegral.integral_eq_integral_of_support_subset, hz]
        intro t ht
        exact ⟨hlc.trans_le (hcmin (subset_closure ht)),
          (hdmax (subset_closure ht)).trans hxhi.le⟩
    have htsp : tsupport p ⊆ Icc l d := closure_minimal hsub isClosed_Icc
    refine ⟨p, contDiff_infty_iff_deriv.mpr ⟨fun x => (hd x).differentiableAt,
      hder.symm ▸ hg⟩, HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsub,
      ?_, hder⟩
    exact htsp.trans (fun x hx => ⟨hal.trans_le hx.1, hx.2.trans_lt (hs hdm).2⟩)
  · have hg0 : g = 0 := by
      funext t
      by_contra h
      exact he ⟨t, subset_closure h⟩
    subst g
    exact ⟨0, contDiff_const, HasCompactSupport.zero, by simp, deriv_zero⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Local distributional constancy for a globally continuous extension.
Only tests supported strictly inside (a,b) are used. -/
theorem constant_on_Ioo (a b : ℝ) (hab : a < b) (f : ℝ → E) (hf : Continuous f)
    (hw : ∀ p : ℝ → ℝ, ContDiff ℝ ∞ p → HasCompactSupport p →
      tsupport p ⊆ Ioo a b → ∫ t, deriv p t • f t = 0) :
    ∃ c : E, EqOn f (fun _ => c) (Ioo a b) := by
  have hfli : LocallyIntegrable f volume := hf.locallyIntegrable
  let m := (a + b) / 2
  let r := (b - a) / 4
  let bump : ContDiffBump m := ⟨r / 2, r, by dsimp [r]; linarith, by dsimp [r]; linarith⟩
  let ρ := bump.normed volume
  have hρ : ContDiff ℝ ∞ ρ := bump.contDiff_normed
  have hcρ : HasCompactSupport ρ := bump.hasCompactSupport_normed
  have hsρ : tsupport ρ ⊆ Ioo a b := by
    rw [bump.tsupport_normed_eq]
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at ht
    dsimp [bump, m, r] at ht
    constructor <;> linarith
  have hiρ : ∫ t, ρ t = 1 := bump.integral_normed
  let c := ∫ t, ρ t • f t
  have hz : ∀ᵐ t, t ∈ Ioo a b → f t - c = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hf.sub continuous_const).continuousOn.locallyIntegrableOn measurableSet_Ioo)
    intro g hg hcg hsg
    let q := fun t => g t - (∫ s, g s) * ρ t
    have hq : ContDiff ℝ ∞ q := hg.sub (contDiff_const.mul hρ)
    have hcq : HasCompactSupport q := hcg.sub hcρ.mul_left
    have hsq : tsupport q ⊆ Ioo a b :=
      (tsupport_sub _ _).trans (union_subset hsg ((tsupport_mul_subset_right (f := fun _ => ∫ s, g s) (g := ρ)).trans hsρ))
    have hzg : ∫ t, q t = 0 := by
      rw [integral_sub (hg.continuous.integrable_of_hasCompactSupport hcg)
        ((hρ.continuous.integrable_of_hasCompactSupport hcρ).const_mul _),
        integral_const_mul, hiρ, mul_one, sub_self]
    obtain ⟨p, hp, hcp, hsp, hpg⟩ := compact_primitive_in a b q hq hcq hsq hzg
    have hzero := hw p hp hcp hsp
    rw [hpg] at hzero
    have hig := hfli.integrable_smul_left_of_hasCompactSupport hg.continuous hcg
    have hir := hfli.integrable_smul_left_of_hasCompactSupport hρ.continuous hcρ
    have hval : (∫ t, g t • f t) - (∫ s, g s) • c = 0 := by
      simp only [q, sub_smul, mul_smul] at hzero
      have him : Integrable (fun t => (∫ s, g s) • (ρ t • f t)) volume := hir.smul _
      rw [integral_sub hig him, integral_smul] at hzero
      exact hzero
    change (∫ t, g t • (f t - c)) = 0
    simp only [smul_sub]
    rw [integral_sub hig ((hg.continuous.integrable_of_hasCompactSupport hcg).smul_const c),
      integral_smul_const]
    exact hval
  refine ⟨c, Measure.eqOn_open_of_ae_eq (μ := volume) ((ae_restrict_iff' measurableSet_Ioo).mpr ?_)
    isOpen_Ioo hf.continuousOn continuousOn_const⟩
  filter_upwards [hz] with t ht htI using sub_eq_zero.mp (ht htI)

end QuantumNLS.Ext005IntervalPrimitiveR111

#print axioms QuantumNLS.Ext005IntervalPrimitiveR111.compact_primitive_in
#print axioms QuantumNLS.Ext005IntervalPrimitiveR111.constant_on_Ioo

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005IntervalPrimitiveR111." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005IntervalPrimitiveR111." then
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
  Lean.logInfo m!"R111 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

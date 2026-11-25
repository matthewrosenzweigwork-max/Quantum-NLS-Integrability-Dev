import Mathlib
import QuantumNLS.Prop025ODer
import QuantumNLS.Prop025OCount

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O3d:
the fixed-contour part of eq:MP-correction-scalar, at the eigenvalue level.

Source (mixed_propagation.tex:320-345): "Let `c_N(t,θ)` be the real scalar obtained from eq:MP-C1 by
replacing `(S_N, S_N')` with `(s, s')`. ... `‖(C_{1,N} − c_N)P_N‖ ≤ C(W_aΔ_N + ρ^I_N)`."  The
fixed-contour part of `C_{1,N}` is `Re (i/2π) ∮_{Γ_n} q̃_z(S_N(z), S_N'(z)) dz`; on the derivative event
`EI_der` (stage O3a, eq:MP-fixed-deviation: `|s_N − s| + |s_N' − s'| ≤ ρ^I_N` on `Γ_n`) its eigenvalue is
within `(2π)⁻¹ length(Γ_n) Lip(q̃) ρ^I_N` of the background scalar.

* `c1bg`: the background scalar `Re (i/2π) ∮_Γ g(z, s(z), s'(z)) dz` (PROP-010 `c1` with `(S_N, S_N')`
  replaced by `(s, s')`).
* **`c1_conc`**: for a bounded Lipschitz extension `g` (PROP-010 `Extension`), a rectangle `Γ` at positive
  distance from `supp μ`, and a label `m` whose roots avoid `Γ` and whose transfer eigenvalue obeys
  `|s_N − s| ≤ ρ`, `|s_N' − s'| ≤ ρ` on `Γ`:
  `|c1(m) − c1bg| ≤ (2π)⁻¹ (2(b−a)+4h) Lip(g) ρ`. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

open Set Filter Topology Complex MeasureTheory Metric

namespace QuantumNLS.Prop025OCorr

open QuantumNLS.Prop010ContourBindingR11
open PhysicalTensor (L2T)
open BetheLabels (MArr)
open Prop017Quantum (qAct)
open PeriodReconstructionCore PeriodReconstruction PeriodTwoTerm

variable (L : ℝ) [Fact (0<L)] {κ : ℝ}

/-- The background scalar of the fixed-contour correction (`(S_N, S_N')` replaced by `(s, s')`). -/
def c1bg (G : ℂ → ℂ) (g : Extension (ℂ × (ℂ × ℂ))) (a b h : ℝ) : ℝ :=
  ((I/(2*Real.pi):ℂ) * LabelExactPeriod.rectIntegral
    (fun z => g.value (z, (sf L κ G z, deriv (sf L κ G) z))) a b h).re

/-- The background transfer is analytic at points at positive distance from the support. -/
theorem analyticAt_sf (μ' : Measure ℝ) [IsProbabilityMeasure μ'] {z : ℂ} {d0 : ℝ} (hd0 : 0 < d0)
    (hz : ∀ t ∈ μ'.support, d0 ≤ ‖z - t‖) :
    AnalyticAt ℂ (sf L κ (EmpiricalRapidity.cauchyTransform μ')) z := by
  have hd : DifferentiableOn ℂ (sf L κ (EmpiricalRapidity.cauchyTransform μ')) (ball z (d0 / 2)) := by
    intro w hw
    refine (Prop025ODer.differentiableAt_sf (differentiableAt_cauchy μ' (d0 := d0 / 2) (by positivity)
      fun t ht => ?_)).differentiableWithinAt
    have h1 := hz t ht
    have h2 : ‖w - z‖ < d0 / 2 := by rwa [mem_ball, dist_eq_norm] at hw
    have h3 := norm_sub_norm_le (z - (t : ℂ)) (z - w)
    have e : z - (t : ℂ) - (z - w) = w - t := by ring
    rw [e, norm_sub_rev z w] at h3
    linarith
  exact hd.analyticAt (ball_mem_nhds z (by positivity))

/-- **eq:MP-correction-scalar, fixed-contour part.** -/
theorem c1_conc (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (m : MArr N) (μ' : Measure ℝ) [IsProbabilityMeasure μ']
    (g : Extension (ℂ × (ℂ × ℂ))) {a b h d0 ρ : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) (hd0 : 0 < d0)
    (hsupp : ∀ z ∈ Gam a b h, ∀ t ∈ μ'.support, d0 ≤ ‖z - t‖)
    (hroot : ∀ w ∈ Gam a b h, ∀ j, w ≠ ((qAct L κ N m j : ℝ) : ℂ))
    (hdev : ∀ w ∈ Gam a b h,
      ‖sNf L (κ / N) (qAct L κ N m) w - sf L κ (EmpiricalRapidity.cauchyTransform μ') w‖ ≤ ρ ∧
      ‖deriv (sNf L (κ / N) (qAct L κ N m)) w -
        deriv (sf L κ (EmpiricalRapidity.cauchyTransform μ')) w‖ ≤ ρ) :
    |c1 L hκ hN g a b h m - c1bg (κ := κ) L (EmpiricalRapidity.cauchyTransform μ') g a b h| ≤
      (2 * Real.pi)⁻¹ * ((2 * (b - a) + 4 * h) * (g.constant * ρ)) := by
  set G := EmpiricalRapidity.cauchyTransform μ' with hG
  have hq : (configuration L hκ hN m).q = qAct L κ N m := configuration_q L hκ hN m
  have hroot' : ∀ w ∈ Gam a b h, ∀ j, w ≠ ((configuration L hκ hN m).q j : ℂ) := by
    intro w hw j; rw [hq]; exact hroot w hw j
  -- continuity of both integrands on `Γ`
  have hev : Differentiable ℂ (fun z => ev L hκ hN z m) :=
    NormalityBridge.eigen_differentiable (L := L) κ hκ hN m
  have hevc : Continuous (fun z => ev L hκ hN z m) := hev.continuous
  have hdevc : Continuous (fun z => dev L hκ hN z m) :=
    (hev.contDiff (n := 1)).continuous_deriv le_rfl
  have hF1 : ∀ z ∈ Gam a b h, ContinuousAt (fun z => g.value (z, (ev L hκ hN z m, dev L hκ hN z m))) z :=
    fun z _ => (g.lipschitz.continuous.comp (continuous_id.prodMk (hevc.prodMk hdevc))).continuousAt
  have hF2 : ∀ z ∈ Gam a b h, ContinuousAt (fun z => g.value (z, (sf L κ G z, deriv (sf L κ G) z))) z := by
    intro z hz
    have ha := analyticAt_sf (κ := κ) L μ' hd0 (hsupp z hz)
    exact g.lipschitz.continuous.continuousAt.comp
      (continuousAt_id.prodMk (ha.continuousAt.prodMk ha.deriv.continuousAt))
  have hsub : LabelExactPeriod.rectIntegral (fun z => g.value (z, (ev L hκ hN z m, dev L hκ hN z m))) a b h -
      LabelExactPeriod.rectIntegral (fun z => g.value (z, (sf L κ G z, deriv (sf L κ G) z))) a b h =
      LabelExactPeriod.rectIntegral (fun z => g.value (z, (ev L hκ hN z m, dev L hκ hN z m)) +
        (-1 : ℂ) * g.value (z, (sf L κ G z, deriv (sf L κ G) z))) a b h := by
    have hadd := rectIntegral_add (f := fun z => g.value (z, (ev L hκ hN z m, dev L hκ hN z m)))
      (g := fun z => (-1 : ℂ) * g.value (z, (sf L κ G z, deriv (sf L κ G) z))) hab hh hF1
      (fun z hz => (continuousAt_const (y := (-1 : ℂ))).mul (hF2 z hz))
    rw [hadd, rectIntegral_const_mul]
    ring
  -- the pointwise Lipschitz bound
  have hpt : ∀ z ∈ Gam a b h, ‖g.value (z, (ev L hκ hN z m, dev L hκ hN z m)) +
      (-1 : ℂ) * g.value (z, (sf L κ G z, deriv (sf L κ G) z))‖ ≤ g.constant * ρ := by
    intro z hz
    rw [ev_configuration L hκ hN m z (hroot' z hz), dev_configuration L hκ hN m z (hroot' z hz), hq]
    have e : ∀ x y : ℂ, x + (-1 : ℂ) * y = x - y := fun x y => by ring
    rw [e, ← dist_eq_norm]
    refine (g.lipschitz.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _))
    obtain ⟨h1, h2⟩ := hdev z hz
    rw [Prod.dist_eq, Prod.dist_eq, dist_self, dist_eq_norm, dist_eq_norm]
    exact max_le ((norm_nonneg _).trans h1) (max_le h1 h2)
  have hint := norm_rectIntegral_le hab hh hpt
  unfold c1 c1bg
  rw [← Complex.sub_re, ← mul_sub, hsub]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul]
  have hn : ‖(I/(2*Real.pi):ℂ)‖ = (2*Real.pi)⁻¹ := by
    rw [norm_div, Complex.norm_I, show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), one_div]
  rw [hn]
  exact mul_le_mul_of_nonneg_left hint (by positivity)

end QuantumNLS.Prop025OCorr

#print axioms QuantumNLS.Prop025OCorr.analyticAt_sf
#print axioms QuantumNLS.Prop025OCorr.c1_conc

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OCorr." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
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
  Lean.logInfo m!"Prop025OCorr aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."

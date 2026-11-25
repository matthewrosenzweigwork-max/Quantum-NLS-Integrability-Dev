import QuantumNLS.LabelExactPeriod

/-!
# PROP-005 (prop:B3-exact-period), owner decision D1 restatement

Owner decision D1 (2026-11-16): a DEF-043 regular cut is EVERY `x ∉ supp μ` with `F(x)/(2π)` not an integer; separation
holds at every such `x`, with the unique integer `a` satisfying `2πa < F(x) < 2π(a+1)`.

Restatement convention (Terra r207): replace `(S : IndexedScalarMeasureCuts L κ)` by `(S : IndexedScalarMeasure L κ)`,
replace each cut-membership hypothesis `x ∈ S.cuts` (both `hxm` and `hxp`) by `x ∉ S.μ.support`, and keep every other
binder, force inequality, hypothesis and conclusion verbatim from `PROP005Spec` (STATUS lines 246-312): both force
intervals, `xm < xp`, `h > 0`, the accepted rectangle integral and the exact complex normalization.  The three
cut-free statements (`root_period_spec`, `spectralValue_polynomial_identity_spec`,
`spectralValue_difference_riccati_spec`) are retained verbatim.

The single headline `exact_period_d1` is the conjunction of the five `PROP005Spec` statements, each as a universally
quantified statement with the accepted binder list.  Proved from the accepted theorems of the frozen module
`LabelExactPeriod` (the two period statements applied to `S.toCuts`).  No hypothesis is added; no frozen module is edited.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace QuantumNLS.D1Prop005

open MeasureTheory Filter Topology Set Complex intervalIntegral
open scoped BigOperators
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS QuantumNLS.LabelExactPeriod

set_option maxHeartbeats 4000000 in
/-- **PROP-005, owner decision D1**: exact period at every pair of exterior points with the stated force levels
(uniform and sequence forms), together with the one-root period, the polynomial transfer identity and the
difference-Riccati identity. -/
theorem exact_period_d1 :
    (∀ {c q a b h : ℝ} (hc : 0 < c) (hch : 2 * c < h) (hqa : 2 * c < |q - a|)
      (hqb : 2 * c < |q - b|) (hab : a < b),
      rectIntegral (fun z => log (1 + I * c / (z - q))) a b h =
        if a < q ∧ q < b then 2 * Real.pi * I * (I * c) else 0) ∧
    (∀ {L κ : ℝ} (S : IndexedScalarMeasure L κ)
      {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {n : ℤ} {xm xp h : ℝ}
      (hxm : xm ∉ S.μ.support) (hxp : xp ∉ S.μ.support) (hlt : xm < xp) (hh : 0 < h)
      (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
      (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
      (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
      (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)),
      ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
        ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
          (((Finset.univ.filter fun j => B.n j = n).card : ℝ) / N : ℂ) =
            -(1 / (2 * Real.pi * κ)) * rectIntegral (ellN κ B.q) xm xp h) ∧
    (∀ {L κ : ℝ} (S : IndexedScalarMeasure L κ)
      {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
      {B : ∀ k, OnShellBethe L κ (N k)}
      (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
      {n : ℤ} {xm xp h : ℝ} (hxm : xm ∉ S.μ.support) (hxp : xp ∉ S.μ.support) (hlt : xm < xp)
      (hh : 0 < h)
      (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
      (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
      (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
      (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)),
      ∀ᶠ k in atTop, (((Finset.univ.filter fun j => (B k).n j = n).card : ℝ) / N k : ℂ) =
        -(1 / (2 * Real.pi * κ)) * rectIntegral (ellN κ (B k).q) xm xp h) ∧
    (∀ (L : ℝ) [Fact (0 < L)] {N : ℕ} {c : ℝ} (hc : 0 < c)
      {n : Fin N → ℤ} (hn : Antitone n) (z : ℂ),
      BetheSpectralContinuity.spectralValue L hc hn z *
          ∏ j, (z - BetheSmooth.sourceRoots L n c j) =
        ∏ j, (z - BetheSmooth.sourceRoots L n c j + I * c) +
          exp (I * L * z) * ∏ j, (z - BetheSmooth.sourceRoots L n c j - I * c)) ∧
    (∀ (L : ℝ) [Fact (0 < L)] {N : ℕ} {c : ℝ} (hc : 0 < c)
      {n : Fin N → ℤ} (hn : Antitone n) {z : ℂ}
      (hz : ∀ j, z ≠ BetheSmooth.sourceRoots L n c j)
      (hz' : ∀ j, z ≠ BetheSmooth.sourceRoots L n c j + I * c),
      BetheSpectralContinuity.spectralValue L hc hn z =
        AN c (BetheSmooth.sourceRoots L n c) z +
          exp (I * L * z) / AN c (BetheSmooth.sourceRoots L n c) (z - I * c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c q a b h hc hch hqa hqb hab
    exact QuantumNLS.LabelExactPeriod.root_period hc hch hqa hqb hab
  · intro L κ S μ hμ n xm xp h hxm hxp hlt hh h1 h2 h3 h4
    exact QuantumNLS.LabelExactPeriod.exact_period_uniform S.toCuts hμ hxm hxp hlt hh h1 h2 h3 h4
  · intro L κ S μ hμ N hN B hconv hNtop n xm xp h hxm hxp hlt hh h1 h2 h3 h4
    exact QuantumNLS.LabelExactPeriod.exact_period_seq S.toCuts hμ hconv hNtop hxm hxp hlt hh
      h1 h2 h3 h4
  · intro L _ N c hc n hn z
    exact QuantumNLS.LabelExactPeriod.spectralValue_polynomial_identity L hc hn z
  · intro L _ N c hc n hn z hz hz'
    exact QuantumNLS.LabelExactPeriod.spectralValue_difference_riccati L hc hn hz hz'

end QuantumNLS.D1Prop005

#print axioms QuantumNLS.D1Prop005.exact_period_d1

import QuantumNLS.LabelBlock

/-!
# PROP-004 (cor:B3-label-block), owner decision D1 restatement

Owner decision D1 (2026-11-16): a DEF-043 regular cut is EVERY `x ∉ supp μ` with `F(x)/(2π)` not an integer; separation
holds at every such `x`, with the unique integer `a` satisfying `2πa < F(x) < 2π(a+1)`.

Restatement convention (Terra r207): replace `(S : IndexedScalarMeasureCuts L κ)` by `(S : IndexedScalarMeasure L κ)`,
replace each cut-membership hypothesis `x ∈ S.cuts` (both `hxm` and `hxp`) by `x ∉ S.μ.support`, and keep every other
binder, force inequality, hypothesis and conclusion verbatim from `PROP004Spec` (STATUS lines 381-431).

The single headline `label_block_d1` is the conjunction of the three `PROP004Spec` statements
(`label_block_uniform_spec`, `label_block_seq_spec`, `label_block_prob_spec`), each as a universally quantified
statement with the accepted binder list.  Proved from the accepted theorems of the frozen module `LabelBlock`
applied to `S.toCuts`.  No hypothesis is added; no frozen module is edited.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace QuantumNLS.D1Prop004

open MeasureTheory Filter Topology Set
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelExactSeparation
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS QuantumNLS.LabelBlock

set_option maxHeartbeats 4000000 in
/-- **PROP-004, owner decision D1**: label block at every pair of exterior points with the stated force levels
(uniform, sequence and probability forms). -/
theorem label_block_d1 :
    (∀ {L κ : ℝ} (S : IndexedScalarMeasure L κ)
      {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {n : ℤ} {xm xp : ℝ}
      (hxm : xm ∉ S.μ.support) (hxp : xp ∉ S.μ.support) (_hlt : xm < xp)
      (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
      (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
      (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
      (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)),
      ∃ δ > 0, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
        ∀ B : OnShellBethe L κ N, rootP B hN ∈ U → BlockConclusion B n xm xp δ) ∧
    (∀ {L κ : ℝ} (S : IndexedScalarMeasure L κ)
      {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
      {B : ∀ k, OnShellBethe L κ (N k)}
      (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
      {n : ℤ} {xm xp : ℝ} (hxm : xm ∉ S.μ.support) (hxp : xp ∉ S.μ.support) (hlt : xm < xp)
      (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
      (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
      (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
      (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)),
      ∃ δ > 0, ∀ᶠ k in atTop, BlockConclusion (B k) n xm xp δ) ∧
    (∀ {L κ : ℝ} (S : IndexedScalarMeasure L κ)
      {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ)
      {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} (hNtop : Tendsto N atTop atTop)
      {B : ∀ k, Ω → OnShellBethe L κ (N k)}
      (hprob : ∀ U ∈ 𝓝 μ, Tendsto (fun k => P {ω | rootP (B k ω) (hN k) ∉ U}) atTop (𝓝 0))
      {n : ℤ} {xm xp : ℝ} (hxm : xm ∉ S.μ.support) (hxp : xp ∉ S.μ.support) (hlt : xm < xp)
      (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
      (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
      (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
      (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)),
      ∃ δ > 0, Tendsto (fun k => P {ω | BlockConclusion (B k ω) n xm xp δ}) atTop (𝓝 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L κ S μ hμ n xm xp hxm hxp _hlt h1 h2 h3 h4
    exact QuantumNLS.LabelBlock.label_block_uniform S.toCuts hμ hxm hxp _hlt h1 h2 h3 h4
  · intro L κ S μ hμ N hN B hconv hNtop n xm xp hxm hxp hlt h1 h2 h3 h4
    exact QuantumNLS.LabelBlock.label_block_seq S.toCuts hμ hconv hNtop hxm hxp hlt h1 h2 h3 h4
  · intro L κ S μ hμ Ω _ P _ N hN hNtop B hprob n xm xp hxm hxp hlt h1 h2 h3 h4
    exact QuantumNLS.LabelBlock.label_block_prob S.toCuts hμ P hNtop hprob hxm hxp hlt h1 h2 h3 h4

end QuantumNLS.D1Prop004

#print axioms QuantumNLS.D1Prop004.label_block_d1

import QuantumNLS.LabelBlock
/-! integrator-authored trusted spec for PROP-004 cor:B3-label-block (Terra r137 ACCEPT; regular-cut qualification): frozen statements restated verbatim. -/
namespace PROP004Spec
open MeasureTheory Filter Topology Set
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelExactSeparation
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS QuantumNLS.LabelBlock

set_option maxHeartbeats 4000000 in
theorem label_block_uniform_spec  {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {n : ℤ} {xm xp : ℝ}
    (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (_hlt : xm < xp)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ δ > 0, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U → BlockConclusion B n xm xp δ := by
  apply QuantumNLS.LabelBlock.label_block_uniform <;> assumption

set_option maxHeartbeats 4000000 in
theorem label_block_seq_spec  {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
    {B : ∀ k, OnShellBethe L κ (N k)}
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
    {n : ℤ} {xm xp : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ δ > 0, ∀ᶠ k in atTop, BlockConclusion (B k) n xm xp δ := by
  apply QuantumNLS.LabelBlock.label_block_seq <;> assumption

set_option maxHeartbeats 4000000 in
theorem label_block_prob_spec  {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} (hNtop : Tendsto N atTop atTop)
    {B : ∀ k, Ω → OnShellBethe L κ (N k)}
    (hprob : ∀ U ∈ 𝓝 μ, Tendsto (fun k => P {ω | rootP (B k ω) (hN k) ∉ U}) atTop (𝓝 0))
    {n : ℤ} {xm xp : ℝ} (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ δ > 0, Tendsto (fun k => P {ω | BlockConclusion (B k ω) n xm xp δ}) atTop (𝓝 1) := by
  apply QuantumNLS.LabelBlock.label_block_prob <;> assumption

end PROP004Spec
#print axioms PROP004Spec.label_block_uniform_spec
#print axioms PROP004Spec.label_block_seq_spec
#print axioms PROP004Spec.label_block_prob_spec

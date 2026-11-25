import QuantumNLS.D1Prop004
/-! integrator-authored trusted spec for PROP-004 D1 restatement (terra_review r208 PASS): headline statement(s) copied verbatim from D1Prop004 (QuantumNLS.D1Prop004). -/
set_option autoImplicit false
set_option linter.unusedVariables false
namespace QuantumNLS.D1P004Spec
open QuantumNLS.D1Prop004
open MeasureTheory Filter Topology Set
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelExactSeparation
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS QuantumNLS.LabelBlock

set_option maxHeartbeats 8000000 in
theorem label_block_d1_spec :
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
  exact QuantumNLS.D1Prop004.label_block_d1 

end QuantumNLS.D1P004Spec
#print axioms QuantumNLS.D1P004Spec.label_block_d1_spec

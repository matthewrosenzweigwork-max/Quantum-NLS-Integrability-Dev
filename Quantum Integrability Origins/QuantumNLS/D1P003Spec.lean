import QuantumNLS.D1Prop003
/-! integrator-authored trusted spec for PROP-003 D1 restatement (terra_review r208 PASS): headline statement(s) copied verbatim from D1Prop003 (QuantumNLS.D1Prop003). -/
set_option autoImplicit false
set_option linter.unusedVariables false
namespace QuantumNLS.D1P003Spec
open QuantumNLS.D1Prop003
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelWeakJointLimit
  QuantumNLS.LabelSeparationCore QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
  QuantumNLS.EmpiricalRapidity
open QuantumNLS QuantumNLS.LabelExactSeparation

set_option maxHeartbeats 8000000 in
theorem exact_separation_d1_spec :
    (∀ {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
      {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)}
      {μ : MeasureTheory.ProbabilityMeasure ℝ} (S : IndexedScalarMeasure L κ)
      (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hμ : (μ : Measure ℝ) = S.μ)
      (hNtop : Tendsto N atTop atTop) {x : ℝ} (hx : x ∉ S.μ.support) {a : ℤ}
      (h1 : 2 * Real.pi * a < exteriorForce L κ S.μ x)
      (h2 : exteriorForce L κ S.μ x < 2 * Real.pi * (a + 1)),
      ∃ δ > 0, ∀ᶠ k in atTop, ∀ j, ((B k).n j ≤ a → (B k).q j < x - δ) ∧
        (a + 1 ≤ (B k).n j → x + δ < (B k).q j)) ∧
    (∀ {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
      {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)}
      {μ : MeasureTheory.ProbabilityMeasure ℝ} {L κ : ℝ} (S : IndexedScalarMeasure L κ)
      {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {x : ℝ} (hx : x ∉ S.μ.support) {a : ℤ}
      (h1 : 2 * Real.pi * a < exteriorForce L κ S.μ x)
      (h2 : exteriorForce L κ S.μ x < 2 * Real.pi * (a + 1)),
      ∃ δ > 0, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
        ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
          ∀ j, (B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j)) ∧
    (∀ {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
      {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)}
      {μ : MeasureTheory.ProbabilityMeasure ℝ} {L κ : ℝ} {N : ℕ} (B : OnShellBethe L κ N) {a : ℤ}
      {x δ : ℝ}
      (h : ∀ j, (B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j)) (j : Fin N),
      B.q j ∉ Icc (x - δ) (x + δ)) ∧
    (∀ {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k}
      {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)}
      {μ : MeasureTheory.ProbabilityMeasure ℝ} {L κ : ℝ} {N : ℕ} (B : OnShellBethe L κ N) {a : ℤ}
      {x δ : ℝ} (hδ : 0 < δ)
      (h : ∀ j, (B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j)) (j : Fin N),
      B.q j < x ↔ B.n j ≤ a) := by
  exact QuantumNLS.D1Prop003.exact_separation_d1 

end QuantumNLS.D1P003Spec
#print axioms QuantumNLS.D1P003Spec.exact_separation_d1_spec

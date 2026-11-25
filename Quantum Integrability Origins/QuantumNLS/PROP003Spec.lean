import QuantumNLS.LabelExactSeparation
/-! integrator-authored trusted spec for PROP-003 thm:B3-exact-separation (Terra r135 ACCEPT; regular-cut reading of x ∉ supp μ): frozen statements restated verbatim. -/
namespace PROP003Spec
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelWeakJointLimit
  QuantumNLS.LabelSeparationCore QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
  QuantumNLS.EmpiricalRapidity
open QuantumNLS QuantumNLS.LabelExactSeparation

set_option maxHeartbeats 4000000 in
theorem exact_separation_seq_spec {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)} {μ : MeasureTheory.ProbabilityMeasure ℝ} (S : IndexedScalarMeasureCuts L κ)
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hμ : (μ : Measure ℝ) = S.μ)
    (hNtop : Tendsto N atTop atTop) {x : ℝ} (hx : x ∈ S.cuts) {a : ℤ}
    (h1 : 2 * Real.pi * a < exteriorForce L κ S.μ x)
    (h2 : exteriorForce L κ S.μ x < 2 * Real.pi * (a + 1)) :
    ∃ δ > 0, ∀ᶠ k in atTop, ∀ j, ((B k).n j ≤ a → (B k).q j < x - δ) ∧
      (a + 1 ≤ (B k).n j → x + δ < (B k).q j) := by
  apply QuantumNLS.LabelExactSeparation.exact_separation_seq <;> assumption

set_option maxHeartbeats 4000000 in
theorem exact_separation_uniform_spec {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)} {μ : MeasureTheory.ProbabilityMeasure ℝ} {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ)
    {μ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) = S.μ) {x : ℝ} (hx : x ∈ S.cuts) {a : ℤ}
    (h1 : 2 * Real.pi * a < exteriorForce L κ S.μ x)
    (h2 : exteriorForce L κ S.μ x < 2 * Real.pi * (a + 1)) :
    ∃ δ > 0, ∃ U ∈ 𝓝 μ, ∃ N₀ : ℕ, ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N →
      ∀ B : OnShellBethe L κ N, rootP B hN ∈ U →
        ∀ j, (B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j) := by
  apply QuantumNLS.LabelExactSeparation.exact_separation_uniform <;> assumption

set_option maxHeartbeats 4000000 in
theorem no_roots_near_spec {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)} {μ : MeasureTheory.ProbabilityMeasure ℝ} {L κ : ℝ} {N : ℕ} (B : OnShellBethe L κ N) {a : ℤ} {x δ : ℝ}
    (h : ∀ j, (B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j)) (j : Fin N) :
    B.q j ∉ Icc (x - δ) (x + δ) := by
  apply QuantumNLS.LabelExactSeparation.no_roots_near <;> assumption

set_option maxHeartbeats 4000000 in
theorem lt_iff_label_le_spec {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)} {μ : MeasureTheory.ProbabilityMeasure ℝ} {L κ : ℝ} {N : ℕ} (B : OnShellBethe L κ N) {a : ℤ} {x δ : ℝ} (hδ : 0 < δ)
    (h : ∀ j, (B.n j ≤ a → B.q j < x - δ) ∧ (a + 1 ≤ B.n j → x + δ < B.q j)) (j : Fin N) :
    B.q j < x ↔ B.n j ≤ a := by
  apply QuantumNLS.LabelExactSeparation.lt_iff_label_le <;> assumption

end PROP003Spec
#print axioms PROP003Spec.exact_separation_seq_spec
#print axioms PROP003Spec.exact_separation_uniform_spec
#print axioms PROP003Spec.no_roots_near_spec
#print axioms PROP003Spec.lt_iff_label_le_spec

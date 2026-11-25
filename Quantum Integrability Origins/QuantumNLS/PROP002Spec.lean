import QuantumNLS.LabelWeakJointLimit
/-! integrator-authored trusted spec for PROP-002 lem:B3-weak-joint-limit (Terra r134 ACCEPT; general N_k → ∞ form): frozen statements of LabelWeakJointLimit restated verbatim. -/
namespace PROP002Spec
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open QuantumNLS.LabelJointLimit QuantumNLS.LabelTightness QuantumNLS.LabelJointWeak
  QuantumNLS.LabelJointStructure QuantumNLS.LabelKernelLimit QuantumNLS.LabelIdentification
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts QuantumNLS.EmpiricalRapidity
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS QuantumNLS.LabelWeakJointLimit
open QuantumNLS.LabelWeakJointLimit

set_option maxHeartbeats 4000000 in
theorem weak_joint_limit_spec {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)} {μ : MeasureTheory.ProbabilityMeasure ℝ} (hL : 0 < L) (hκ : 0 < κ) [NullSingletonClass (μ : Measure ℝ)]
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    (hNtop : Tendsto N atTop atTop) {reG : ℝ → ℝ}
    (hbd : LocallyUniformBoundary (μ : Measure ℝ) reG ∨ BoundedAEBoundary (μ : Measure ℝ) reG)
    {n : ℝ → ℤ} (hnI : ∀ᵐ t ∂(μ : Measure ℝ), (n t : ℝ) = indexLabel L κ reG t) :
    Tendsto (fun k => jointP (B k) (hN k)) atTop (𝓝 (graphP μ n)) := by
  apply QuantumNLS.LabelWeakJointLimit.weak_joint_limit <;> assumption

set_option maxHeartbeats 4000000 in
theorem weak_joint_limit_DEF043_spec {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)} {μ : MeasureTheory.ProbabilityMeasure ℝ} (S : IndexedScalarMeasureCuts L κ)
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    (hμ : (μ : Measure ℝ) = S.μ) (hNtop : Tendsto N atTop atTop) :
    (∃ n : ℝ → ℤ, Measurable n ∧ ∀ᵐ t ∂S.μ, (n t : ℝ) = indexLabel L κ S.reG t) ∧
    ∀ n : ℝ → ℤ, (∀ᵐ t ∂S.μ, (n t : ℝ) = indexLabel L κ S.reG t) →
      Tendsto (fun k => jointP (B k) (hN k)) atTop (𝓝 (graphP μ n)) := by
  apply QuantumNLS.LabelWeakJointLimit.weak_joint_limit_DEF043 <;> assumption

set_option maxHeartbeats 4000000 in
theorem weak_joint_limit_DEF010_spec {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)} {μ : MeasureTheory.ProbabilityMeasure ℝ} (S : IndexedScalarMeasureCuts L κ) (m : ∀ k, MArr (N k))
    (hq : ∀ k, (B k).q = arrRoots L (κ / N k) (m k))
    (hconv : Tendsto (fun k => empiricalP L κ (hN k) (m k)) atTop (𝓝 μ))
    (hμ : (μ : Measure ℝ) = S.μ) (hNtop : Tendsto N atTop atTop) :
    (∃ n : ℝ → ℤ, Measurable n ∧ ∀ᵐ t ∂S.μ, (n t : ℝ) = indexLabel L κ S.reG t) ∧
    ∀ n : ℝ → ℤ, (∀ᵐ t ∂S.μ, (n t : ℝ) = indexLabel L κ S.reG t) →
      Tendsto (fun k => jointP (B k) (hN k)) atTop (𝓝 (graphP μ n)) := by
  apply QuantumNLS.LabelWeakJointLimit.weak_joint_limit_DEF010 <;> assumption

set_option maxHeartbeats 4000000 in
theorem exists_label_version_spec {L κ : ℝ} {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, QuantumNLS.LabelJointLimit.OnShellBethe L κ (N k)} {μ : MeasureTheory.ProbabilityMeasure ℝ} (hL : 0 < L) (hκ : 0 < κ) [NullSingletonClass (μ : Measure ℝ)]
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    (hNtop : Tendsto N atTop atTop) {reG : ℝ → ℝ}
    (hbd : LocallyUniformBoundary (μ : Measure ℝ) reG ∨ BoundedAEBoundary (μ : Measure ℝ) reG) :
    ∃ n : ℝ → ℤ, Measurable n ∧ ∀ᵐ t ∂(μ : Measure ℝ), (n t : ℝ) = indexLabel L κ reG t := by
  apply QuantumNLS.LabelWeakJointLimit.exists_label_version <;> assumption

end PROP002Spec
#print axioms PROP002Spec.weak_joint_limit_spec
#print axioms PROP002Spec.weak_joint_limit_DEF043_spec
#print axioms PROP002Spec.weak_joint_limit_DEF010_spec
#print axioms PROP002Spec.exists_label_version_spec

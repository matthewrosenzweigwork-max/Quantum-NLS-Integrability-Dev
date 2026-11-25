import QuantumNLS.Ext025GP12R27m
/-! integrator-authored trusted spec for EXT-025 contract_GP12_fixed (contract ACCEPT): headline statement(s) copied verbatim from Ext025GP12R27m (QuantumNLS.Ext025GP12R27m). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace
namespace QuantumNLS.X25GP12Spec
open QuantumNLS.Ext025GP12R27m
open TraceClass TraceIdeal Ext025STrace Ext025B7GentleCompression EnergyTracePassage
open BetheChargeResolution Ext025B6PVM Ext025B8BorelCalculus
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*} {l : Filter J} [l.NeBot]

set_option maxHeartbeats 8000000 in
theorem contract_GP12_fixed_spec :
    (∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ≥0∞),
      (∀ n, Measurable (f n)) →
      (∫⁻ x, liminf (fun n => f n x) atTop ∂μ) ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop) ∧
    (∀ (P : ProjectionMeasure E) (b : HilbertBasis ι ℂ E)
      (h : ℝ → ℝ), (∀ t, 0 ≤ h t) → Measurable h →
      ∀ (ρ : ℕ → E →L[ℂ] E) (σ : E →L[ℂ] E),
      (∀ n, (ρ n).IsPositive ∧ IsTraceClass (ρ n)) →
      σ.IsPositive ∧ IsTraceClass σ →
      Tendsto (fun n => traceNorm (ρ n-σ)) atTop (𝓝 0) →
      formEnergy P b (fun t => ENNReal.ofReal (h t)) σ ≤
        liminf (fun k => formEnergy P b (fun t => ENNReal.ofReal (h t)) (ρ k)) atTop) ∧
    (∀ {X : Type*} [TopologicalSpace X] (P : ProjectionMeasure E) (b : HilbertBasis ι ℂ E)
      (h : ℝ → ℝ), (∀ t, 0 ≤ h t) → Measurable h →
      ∀ (ρ : X → E →L[ℂ] E), (∀ x, (ρ x).IsPositive ∧ IsTraceClass (ρ x)) →
      (∀ x, Tendsto (fun y => traceNorm (ρ y-ρ x)) (𝓝 x) (𝓝 0)) →
      LowerSemicontinuous (fun x => formEnergy P b (fun t => ENNReal.ofReal (h t)) (ρ x))) ∧
    (∀ (P : ProjectionMeasure E) (h : ℝ → ℝ), (∀ t, 0 ≤ h t) → Measurable h →
      LowerSemicontinuous (Ext025B7PVMForms.energy P (fun t => ENNReal.ofReal (h t)))) := by
  exact QuantumNLS.Ext025GP12R27m.contract_GP12_fixed 

end QuantumNLS.X25GP12Spec
#print axioms QuantumNLS.X25GP12Spec.contract_GP12_fixed_spec

import QuantumNLS.Ext025LGP11
/-! integrator-authored trusted spec for EXT-025 contract_GP11 (terra_review r234 ACCEPT): headline statement(s) copied verbatim from Ext025LGP11 (QuantumNLS.Ext025L). -/
set_option autoImplicit false
universe u v
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace QuantumNLS.X25GP11Spec
open QuantumNLS.Ext025L


set_option maxHeartbeats 8000000 in
theorem contract_GP11_spec :
    -- general measure space
    (∀ (α : Type u) [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ≥0∞),
      (∀ n, Measurable (f n)) → (∀ x, Monotone fun n => f n x) →
      (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (⨆ n, f n x))) ∧
      Monotone (fun n => ∫⁻ x, f n x ∂μ) ∧
      Tendsto (fun n => ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, ⨆ n, f n x ∂μ)) ∧
      (∫⁻ x, ⨆ n, f n x ∂μ) = ⨆ n, ∫⁻ x, f n x ∂μ) ∧
    -- counting measure: nonnegative series, no absolute convergence presumption
    (∀ (ι : Type v) (a : ℕ → ι → ℝ≥0∞), (∀ i, Monotone fun n => a n i) →
      Monotone (fun n => ∑' i, a n i) ∧
      Tendsto (fun n => ∑' i, a n i) atTop (𝓝 (∑' i, ⨆ n, a n i)) ∧
      (∑' i, ⨆ n, a n i) = ⨆ n, ∑' i, a n i) ∧
    -- rearrangement of nonnegative series
    (∀ (ι : Type v) (κ : Type v) (b : ι → κ → ℝ≥0∞),
      (∑' i, ∑' j, b i j) = ∑' j, ∑' i, b i j) ∧
    (∀ (ι : Type v) (κ : Type v) (e : ι ≃ κ) (c : κ → ℝ≥0∞),
      (∑' i, c (e i)) = ∑' j, c j) := by
  exact QuantumNLS.Ext025L.contract_GP11 

end QuantumNLS.X25GP11Spec
#print axioms QuantumNLS.X25GP11Spec.contract_GP11_spec

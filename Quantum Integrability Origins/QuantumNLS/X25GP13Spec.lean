import QuantumNLS.Ext025LGP13
/-! integrator-authored trusted spec for EXT-025 contract_GP13 (terra_review r234 ACCEPT): headline statement(s) copied verbatim from Ext025LGP13 (QuantumNLS.Ext025L). -/
set_option autoImplicit false
universe u v
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace QuantumNLS.X25GP13Spec
open QuantumNLS.Ext025L


set_option maxHeartbeats 8000000 in
theorem contract_GP13_spec :
    -- dominated convergence for the integrals and the L¹ error
    (∀ (𝕜 : Type) [RCLike 𝕜] (α : Type u) [MeasurableSpace α] (μ : Measure α)
      (f : ℕ → α → 𝕜) (g : α → 𝕜) (b : α → ℝ),
      (∀ n, AEStronglyMeasurable (f n) μ) → Integrable b μ →
      (∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ b x) →
      (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
      Integrable g μ ∧
      Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) ∧
      Tendsto (fun n => ∫ x, ‖f n x - g x‖ ∂μ) atTop (𝓝 0)) ∧
    -- the same applied to squares: squared domination gives squared-norm convergence
    (∀ (𝕜 : Type) [RCLike 𝕜] (α : Type u) [MeasurableSpace α] (μ : Measure α)
      (f : ℕ → α → 𝕜) (g : α → 𝕜) (b : α → ℝ),
      (∀ n, AEStronglyMeasurable (f n) μ) → Integrable b μ →
      (∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ^ 2 ≤ b x) →
      (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) →
      (∀ᵐ x ∂μ, ‖g x‖ ^ 2 ≤ b x) ∧
      Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) ∧
    -- counting measure on an arbitrary index set: Fourier-type sums
    (∀ (𝕜 : Type) [RCLike 𝕜] (ι : Type v) (f : ℕ → ι → 𝕜) (g : ι → 𝕜) (b : ι → ℝ),
      Summable b → (∀ n i, ‖f n i‖ ≤ b i) →
      (∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i))) →
      Tendsto (fun n => ∑' i, f n i) atTop (𝓝 (∑' i, g i)) ∧
      Tendsto (fun n => ∑' i, ‖f n i - g i‖) atTop (𝓝 0)) ∧
    (∀ (𝕜 : Type) [RCLike 𝕜] (ι : Type v) (f : ℕ → ι → 𝕜) (g : ι → 𝕜) (b : ι → ℝ),
      Summable b → (∀ n i, ‖f n i‖ ^ 2 ≤ b i) →
      (∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i))) →
      Tendsto (fun n => ∑' i, ‖f n i - g i‖ ^ 2) atTop (𝓝 0)) := by
  exact QuantumNLS.Ext025L.contract_GP13 

end QuantumNLS.X25GP13Spec
#print axioms QuantumNLS.X25GP13Spec.contract_GP13_spec

import QuantumNLS.Ext025LGP10
/-! integrator-authored trusted spec for EXT-025 contract_GP10 (terra_review r234 ACCEPT): headline statement(s) copied verbatim from Ext025LGP10 (QuantumNLS.Ext025L). -/
set_option autoImplicit false
universe u
noncomputable section
open MeasureTheory Filter Topology
open scoped CompactlySupported NNReal
namespace QuantumNLS.X25GP10Spec
open QuantumNLS.Ext025L


set_option maxHeartbeats 8000000 in
theorem contract_GP10_spec :
    -- (1) every mass-bounded sequence has a vaguely convergent subsequence
    (∀ (C : ℝ≥0) (u : ℕ → FiniteMeasure ℝ), (∀ n, (u n).mass ≤ C) →
      ∃ (μ : FiniteMeasure ℝ) (φ : ℕ → ℕ), μ.mass ≤ C ∧ StrictMono φ ∧
        ∀ f : C_c(ℝ, ℝ), Tendsto (fun n => ∫ x, f x ∂(u (φ n))) atTop (𝓝 (∫ x, f x ∂μ))) ∧
    -- (2) vague convergence plus convergence of masses gives weak convergence
    (∀ (ι : Type u) (L : Filter ι) (u : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ),
      (∀ f : C_c(ℝ, ℝ), Tendsto (fun i => ∫ x, f x ∂(u i)) L (𝓝 (∫ x, f x ∂μ))) →
      Tendsto (fun i => ((u i).mass : ℝ)) L (𝓝 (μ.mass : ℝ)) →
      (∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun i => ∫ x, f x ∂(u i)) L (𝓝 (∫ x, f x ∂μ))) ∧
      (∀ f : BoundedContinuousFunction ℝ ℂ,
        Tendsto (fun i => ∫ x, f x ∂(u i)) L (𝓝 (∫ x, f x ∂μ))) ∧
      Tendsto u L (𝓝 μ)) := by
  exact QuantumNLS.Ext025L.contract_GP10 

end QuantumNLS.X25GP10Spec
#print axioms QuantumNLS.X25GP10Spec.contract_GP10_spec

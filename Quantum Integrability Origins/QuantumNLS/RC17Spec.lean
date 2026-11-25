import QuantumNLS.EnergyFormPassR20
/-! integrator-authored trusted spec for R-C17D95AA lem:energy-form-pass (review record r30 FULL ACCEPT): headline statement(s) copied verbatim from EnergyFormPassR20 (QuantumNLS.EnergyFormPassR20). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.RC17Spec
open QuantumNLS.EnergyFormPassR20
open BoundedInverseR13 InverseSquareRootR13 CFCCutoffsR13 ArbitraryEnergyTraceR13
open TraceClass TraceIdeal EnergyForm Ext025B11TracePairing Ext025A12Trace Ext025A12Normal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A)

set_option maxHeartbeats 8000000 in
theorem R_C17D95AA_spec {T : Type*}
    (ρ : ℕ → T → FiniteEnergy A hA h) (σ : T → FiniteEnergy A hA h)
    (B : ℝ) (hB : 0 ≤ B)
    (hρ : ∀ n t, energyTraceNorm (rootInv A hA h) (ρ n t).val ≤ ENNReal.ofReal B)
    (hσ : ∀ t, energyTraceNorm (rootInv A hA h) (σ t).val ≤ ENNReal.ofReal B)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ t,
      traceNorm ((ρ n t).val-(σ t).val) ≤ ENNReal.ofReal δ)
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) :
    TendstoUniformly (fun n t => expectation A hA h K (ρ n t))
      (fun t => expectation A hA h K (σ t)) atTop ∧
    Tendsto (fun n => ⨆ t,
      ‖expectation A hA h K (ρ n t)-expectation A hA h K (σ t)‖) atTop (𝓝 0) ∧
    Tendsto (fun n => ⨆ t, ENNReal.ofReal
      ‖expectation A hA h K (ρ n t)-expectation A hA h K (σ t)‖) atTop (𝓝 0) := by
  exact QuantumNLS.EnergyFormPassR20.R_C17D95AA A hA h ρ σ B hB hρ hσ hconv K hK

end QuantumNLS.RC17Spec
#print axioms QuantumNLS.RC17Spec.R_C17D95AA_spec

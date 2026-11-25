import QuantumNLS.SourceEnergyRealizationR13
/-! integrator-authored trusted spec for R-6EA807B1 source energy-sum form (review record r13 FULL ACCEPT): headline statement(s) copied verbatim from SourceEnergyRealizationR13 (QuantumNLS.SourceEnergyRealizationR13). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.R6EA8SpecB
open QuantumNLS.SourceEnergyRealizationR13
open BoundedInverseR13 InverseSquareRootR13 ArbitraryEnergyTraceR13 PositiveSeriesR13
open TraceClass EnergyForm
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A)

set_option maxHeartbeats 8000000 in
theorem R_6EA807B1_source_spec {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : T → (half A hA h).domain)
    (hf : Continuous (fun t => ((f t : E),half A hA h (f t))))
    (hunit : ∀ t, ‖(f t : E)‖ = 1)
    (ρ : ℕ → T → SourceDensity A hA h)
    (htrace : ∀ n t, posTrace (ρ n t).density = 1)
    (hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ∀ t,
      traceNorm ((ρ n t).density-InnerProductSpace.rankOne ℂ (f t : E) (f t : E)) ≤ ENNReal.ofReal ε)
    (henergy : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ∀ t,
      |sourceEnergy A hA h (ρ n t)-‖half A hA h (f t)‖^2| ≤ ε) :
    Filter.Tendsto (fun n => ⨆ t,
      energyTraceNorm (rootInv A hA h)
        ((ρ n t).density-InnerProductSpace.rankOne ℂ (f t : E) (f t : E))) Filter.atTop (nhds 0) := by
  first
  | exact QuantumNLS.SourceEnergyRealizationR13.R_6EA807B1_source
  | (apply QuantumNLS.SourceEnergyRealizationR13.R_6EA807B1_source <;> assumption)

end QuantumNLS.R6EA8SpecB
#print axioms QuantumNLS.R6EA8SpecB.R_6EA807B1_source_spec

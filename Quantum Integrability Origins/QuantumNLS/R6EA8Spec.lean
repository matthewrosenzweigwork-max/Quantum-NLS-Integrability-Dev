import QuantumNLS.ArbitraryEnergyTraceR13
/-! integrator-authored trusted spec for R-6EA807B1 lem:energy-energy-trace (review record r13 FULL ACCEPT): headline statement(s) copied verbatim from ArbitraryEnergyTraceR13 (QuantumNLS.ArbitraryEnergyTraceR13). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.R6EA8Spec
open QuantumNLS.ArbitraryEnergyTraceR13
open BoundedInverseR13 InverseSquareRootR13 CFCCutoffsR13
open TraceClass EnergyForm EnergyTracePassage EnergyTraceLimit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A)

set_option maxHeartbeats 8000000 in
theorem R_6EA807B1_spec {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : T → (half A hA h).domain)
    (hf : Continuous (fun t => ((f t : E),half A hA h (f t))))
    (_hunit : ∀ t, ‖(f t : E)‖ = 1)
    (ρ : ℕ → T → FiniteEnergy A hA h)
    (_htrace : ∀ n t, posTrace (ρ n t).val = 1)
    (hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      traceNorm ((ρ n t).val-InnerProductSpace.rankOne ℂ (f t : E) (f t : E)) ≤ ENNReal.ofReal ε)
    (henergy : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      |(energyTraceNorm (rootInv A hA h) (ρ n t).val).toReal-‖half A hA h (f t)‖^2| ≤ ε) :
    Tendsto (fun n => ⨆ t,
      energyTraceNorm (rootInv A hA h)
        ((ρ n t).val-InnerProductSpace.rankOne ℂ (f t : E) (f t : E))) atTop (𝓝 0) := by
  first
  | exact QuantumNLS.ArbitraryEnergyTraceR13.R_6EA807B1
  | (apply QuantumNLS.ArbitraryEnergyTraceR13.R_6EA807B1 <;> assumption)

end QuantumNLS.R6EA8Spec
#print axioms QuantumNLS.R6EA8Spec.R_6EA807B1_spec

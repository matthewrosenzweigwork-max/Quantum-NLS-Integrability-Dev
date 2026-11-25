import QuantumNLS.QuantileCore
/-! integrator-authored trusted spec for R-1602B09D CC:F03:core, printed-hypotheses bridge (review record r10 ACCEPT): headline statement(s) copied verbatim from QuantileCore (QuantumNLS.QuantileCore). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal ContDiff Real
noncomputable section
namespace QuantumNLS.R1602SpecC
open QuantumNLS.QuantileCore
open QuantumNLS.QuantileTransport (quantile qm map_qm measurable_qm qm_of_mem leb01)
open QuantumNLS.BulkResponseForm
open QuantumNLS.QuantileForm
open QuantumNLS.FormCore (CoreHyp muRho formN formE formL2 dq core_density' formE_le_lip)

set_option maxHeartbeats 8000000 in
theorem coreHyp_of_coreDensity_spec (μ : Measure ℝ) (hp : IsProbabilityMeasure μ) (hc : CoreDensity μ) :
    ∃ ρ : ℝ → ℝ, CoreHyp ρ ∧ μ = muRho ρ := by
  first
  | exact QuantumNLS.QuantileCore.coreHyp_of_coreDensity
  | (apply QuantumNLS.QuantileCore.coreHyp_of_coreDensity <;> assumption)

end QuantumNLS.R1602SpecC
#print axioms QuantumNLS.R1602SpecC.coreHyp_of_coreDensity_spec

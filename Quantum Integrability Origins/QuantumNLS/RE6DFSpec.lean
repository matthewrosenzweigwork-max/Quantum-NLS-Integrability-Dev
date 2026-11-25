import QuantumNLS.RootOccupationLimit
/-! integrator-authored trusted spec for R-E6DFC650 thm:root-occupation-limit (review record r17 FULL ACCEPT): headline statement(s) copied verbatim from RootOccupationLimit (QuantumNLS.RootOccupationLimit). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace QuantumNLS.RE6DFSpec
open QuantumNLS.RootOccupationLimit
open QuantumNLS.RootOccupationDet QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis empiricalProb IsLimitingRapidityMeasure)
open PhysicalTensor (L2T)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_occupation_limit_spec (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (g : BetheOccupationGauge.Gauge) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun N : ℕ =>
      bornMeasure (BetheOccupationGauge.gaugedBasis (physBasis L hκ N) g) u hu
        {m | ε < ∑' n, |(m.1 n : ℝ) / N - (RootIndexedMasses.masses hκ u).1 n|})
      atTop (𝓝 0)) ∧
    (∀ p : ℝ, 0 < p → Tendsto (fun N : ℕ =>
      ∫ m, (∑' n, |(m.1 n : ℝ) / N - (RootIndexedMasses.masses hκ u).1 n|) ^ p
        ∂(bornMeasure (BetheOccupationGauge.gaugedBasis (physBasis L hκ N) g) u hu))
      atTop (𝓝 0)) ∧
    (∀ N : ℕ, 0 < N → Summable (fun n : ℤ =>
      |∫ m, (m.1 n : ℝ) / N
          ∂(bornMeasure (BetheOccupationGauge.gaugedBasis (physBasis L hκ N) g) u hu) -
        (RootIndexedMasses.masses hκ u).1 n|)) ∧
    Tendsto (fun N : ℕ => ∑' n : ℤ,
      |∫ m, (m.1 n : ℝ) / N
          ∂(bornMeasure (BetheOccupationGauge.gaugedBasis (physBasis L hκ N) g) u hu) -
        (RootIndexedMasses.masses hκ u).1 n|) atTop (𝓝 0) := by
  exact QuantumNLS.RootOccupationLimit.root_occupation_limit hκ u hu g

end QuantumNLS.RE6DFSpec
#print axioms QuantumNLS.RE6DFSpec.root_occupation_limit_spec

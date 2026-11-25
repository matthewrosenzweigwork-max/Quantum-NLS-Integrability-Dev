import QuantumNLS.Reg003CellLocalization
/-! integrator-authored trusted spec for REG-003 CC:limiting-cell-localization (review record r18 FULL ACCEPT): headline statement(s) copied verbatim from Reg003CellLocalization (QuantumNLS.Reg003). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace QuantumNLS.REG3Spec
open QuantumNLS.Reg003
open QuantumNLS.RootOccupationDet QuantumNLS.RootOccupationLimit QuantumNLS.LabelJointLimit
  QuantumNLS.LabelJointWeak QuantumNLS.LabelWeakJointLimit QuantumNLS.IndexedScalarMeasure
  QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis empiricalProb IsLimitingRapidityMeasure)
open PhysicalTensor (L2T)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem reg003_spec (hκ : 0 < κ) (u : L2T L) :
    (∀ n : ℤ, ∀ᵐ t ∂(PhysicalQuantumMeasure.measure hκ u), t ∈ cell hκ u n →
      t ∈ Icc (2 * Real.pi * n / L - 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))
        (2 * Real.pi * n / L + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))) ∧
    (∀ n : ℤ, ((PhysicalQuantumMeasure.measure hκ u).restrict (cell hκ u n)).support ⊆
      Icc (2 * Real.pi * n / L - 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))
        (2 * Real.pi * n / L + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))) ∧
    (∀ n : ℤ, 0 < (RootIndexedMasses.masses hκ u).1 n →
      closure (cell hκ u n ∩ {x | 0 < RootDensityIdentification.dens κ u x}) ⊆
        Icc (2 * Real.pi * n / L - 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))
          (2 * Real.pi * n / L + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L))) ∧
    ∀ s : ℝ, 0 ≤ s →
      (ENNReal.ofReal ((1 + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L)) ^ (-s)) *
          ∑' n : ℤ, ENNReal.ofReal ((1 + |2 * Real.pi * n / L|) ^ s *
            (RootIndexedMasses.masses hκ u).1 n) ≤
        ∫⁻ x, ENNReal.ofReal ((1 + |x|) ^ s) ∂(PhysicalQuantumMeasure.measure hκ u)) ∧
      (∫⁻ x, ENNReal.ofReal ((1 + |x|) ^ s) ∂(PhysicalQuantumMeasure.measure hκ u) ≤
        ENNReal.ofReal ((1 + 2 * Real.sqrt (κ * ‖u‖ ^ 2 / L)) ^ s) *
          ∑' n : ℤ, ENNReal.ofReal ((1 + |2 * Real.pi * n / L|) ^ s *
            (RootIndexedMasses.masses hκ u).1 n)) := by
  exact QuantumNLS.Reg003.reg003 hκ u

end QuantumNLS.REG3Spec
#print axioms QuantumNLS.REG3Spec.reg003_spec

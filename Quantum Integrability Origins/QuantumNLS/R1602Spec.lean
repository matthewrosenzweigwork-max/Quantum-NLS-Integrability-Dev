import QuantumNLS.RootCoreH1
/-! integrator-authored trusted spec for R-1602B09D CC:F03:core (review record r10 ACCEPT): headline statement(s) copied verbatim from RootCoreH1 (QuantumNLS.RootCoreH1). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Real
noncomputable section
namespace QuantumNLS.R1602Spec
open QuantumNLS.RootCoreH1
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.PhysicalQuantumMeasure (measure)
open QuantumNLS.BulkResponseActual (IsPeriodicRepresentative)
open QuantumNLS.FormCore (formN Approx)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem coreDensity_unitH1_spec (hκ : 0 < κ) {u : L2T L} (hu0 : u ≠ 0)
    (hu : QuantumNLS.ProductEnergyPreparation.OneH1 u) :
    QuantumNLS.BulkResponseForm.CoreDensity (measure hκ u) := by
  first
  | exact QuantumNLS.RootCoreH1.coreDensity_unitH1
  | (apply QuantumNLS.RootCoreH1.coreDensity_unitH1 <;> assumption)

set_option maxHeartbeats 8000000 in
theorem core_unitH1_spec (hκ : 0 < κ) {u : L2T L} (hu0 : u ≠ 0)
    (hu : QuantumNLS.ProductEnergyPreparation.OneH1 u) {h : ℝ → ℝ} (hh : Measurable h)
    (hN : formN (measure hκ u) h < ⊤) : Approx (measure hκ u) h := by
  first
  | exact QuantumNLS.RootCoreH1.core_unitH1
  | (apply QuantumNLS.RootCoreH1.core_unitH1 <;> assumption)

end QuantumNLS.R1602Spec
#print axioms QuantumNLS.R1602Spec.coreDensity_unitH1_spec
#print axioms QuantumNLS.R1602Spec.core_unitH1_spec

import QuantumNLS.FormCoreMollifyFinal
/-! integrator-authored trusted spec for R-1602B09D CC:F03:core, generic density (review record r10 ACCEPT): headline statement(s) copied verbatim from FormCoreMollifyFinal (QuantumNLS.FormCore). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Real
noncomputable section
namespace QuantumNLS.R1602SpecB
open QuantumNLS.FormCore
variable {ρ : ℝ → ℝ}

set_option maxHeartbeats 8000000 in
theorem core_density'_spec (H : CoreHyp ρ) {h : ℝ → ℝ} (hh : Measurable h) (hN : formN (muRho ρ) h < ⊤) :
    Approx (muRho ρ) h := by
  first
  | exact QuantumNLS.FormCore.core_density'
  | (apply QuantumNLS.FormCore.core_density' <;> assumption)

end QuantumNLS.R1602SpecB
#print axioms QuantumNLS.R1602SpecB.core_density'_spec

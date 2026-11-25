import QuantumNLS.RiccatiDischarge
/-! integrator-authored trusted spec for R-3FEAD88B values:prop:riccati, interface (review record r36 FULL support): headline statement(s) copied verbatim from RiccatiDischarge (QuantumNLS.RiccatiDischarge). -/
set_option autoImplicit false
noncomputable section
open Set
namespace QuantumNLS.R3FEASpec
open QuantumNLS.RiccatiDischarge
open QuantumNLS.SmoothScalarMomentsPrerequisite QuantumNLS.ClassicalCharges
open QuantumNLS.RiccatiFourierBase QuantumNLS.RiccatiMainFull

set_option maxHeartbeats 8000000 in
theorem riccati_printed_conclusion_of_smooth_spec (L : ℝ) [Fact (0 < L)] {f : ℝ → ℂ}
    (hf : SmoothPeriodic L f) : RiccatiPrintedConclusion L f := by
  exact QuantumNLS.RiccatiDischarge.riccati_printed_conclusion_of_smooth L hf

end QuantumNLS.R3FEASpec
#print axioms QuantumNLS.R3FEASpec.riccati_printed_conclusion_of_smooth_spec

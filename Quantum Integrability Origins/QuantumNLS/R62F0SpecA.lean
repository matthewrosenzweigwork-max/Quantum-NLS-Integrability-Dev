import QuantumNLS.F07StepsR6
/-! integrator-authored trusted spec for R-62F0B724 CC:F07:root-stability, label contraction (Terra r157 FULL ACCEPT): headline statement(s) copied verbatim from F07StepsR6 (QuantumNLS.F07StepsR6). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Set MeasureTheory
namespace QuantumNLS.R62F0SpecA
open QuantumNLS.F07StepsR6


set_option maxHeartbeats 8000000 in
theorem label_contraction_spec {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (p p' : Fin N → ℝ) :
    Real.sqrt (∑ i, (BetheSmooth.root L (F07Round6.freeForce L p') c i -
      BetheSmooth.root L (F07Round6.freeForce L p) c i)^2) ≤
    Real.sqrt (∑ i, (p' i - p i)^2) := by
  first
  | exact QuantumNLS.F07StepsR6.label_contraction
  | (apply QuantumNLS.F07StepsR6.label_contraction <;> assumption)

end QuantumNLS.R62F0SpecA
#print axioms QuantumNLS.R62F0SpecA.label_contraction_spec

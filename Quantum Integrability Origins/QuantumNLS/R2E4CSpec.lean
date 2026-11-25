import QuantumNLS.A06Domains
/-! integrator-authored trusted spec for R-2E4C2F4E A06:domains (Terra r156 ACCEPT): headline statement(s) copied verbatim from A06Domains. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology Function MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal LinearPMap
namespace QuantumNLS.R2E4CSpec
open QuantumNLS.A06Domains
open BetheSpectralCharges BetheCoefficientTransform PhysicalTensor BetheLabels BoundedBetheTransfer
open Ext025B6GraphCore Ext025B9JointGraph Ext025B7JointResolution
variable {L : ℝ} [Fact (0 < L)] {N d : ℕ}

set_option maxHeartbeats 8000000 in
theorem R_2E4C2F4E_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N)
    (c : ℝ) (hc : 0 < c) : Statement (bethe L N hN c hc) := by
  first
  | exact QuantumNLS.A06Domains.R_2E4C2F4E
  | (apply QuantumNLS.A06Domains.R_2E4C2F4E <;> assumption)

end QuantumNLS.R2E4CSpec
#print QuantumNLS.A06Domains.Statement
#print axioms QuantumNLS.R2E4CSpec.R_2E4C2F4E_spec

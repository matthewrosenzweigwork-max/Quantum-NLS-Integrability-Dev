import QuantumNLS.A06Hamiltonian
/-! integrator-authored trusted spec for R-66C3BDD2 A06:hamiltonian (Terra r158 FULL ACCEPT): headline statement(s) copied verbatim from A06Hamiltonian (QuantumNLS.A06Hamiltonian). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology
open scoped InnerProductSpace BigOperators LinearPMap
namespace QuantumNLS.R66C3Spec
open QuantumNLS.A06Hamiltonian
open BetheSpectralCharges BetheCoefficientTransform PhysicalTensor BetheLabels
open BoundedBetheTransfer Ext025B6GraphCore
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

set_option maxHeartbeats 8000000 in
theorem R_66C3BDD2_spec (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N)
    (c : ℝ) (hc : 0 < c) (H : HN L N →ₗ.[ℂ] HN L N)
    (hH : IsSelfAdjoint H)
    (hm : ∀ m, A06Domains.bethe L N hN c hc m ∈ H.domain)
    (he : ∀ m, H ⟨A06Domains.bethe L N hN c hc m,hm m⟩ =
      (eigenvalue L N c 2 m : ℂ) • A06Domains.bethe L N hN c hc m) :
    Statement (A06Domains.bethe L N hN c hc) c H := by
  first
  | exact QuantumNLS.A06Hamiltonian.R_66C3BDD2
  | (apply QuantumNLS.A06Hamiltonian.R_66C3BDD2 <;> assumption)

end QuantumNLS.R66C3Spec
#print axioms QuantumNLS.R66C3Spec.R_66C3BDD2_spec

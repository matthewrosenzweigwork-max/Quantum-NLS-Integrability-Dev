import QuantumNLS.Ext025HGP01
/-! integrator-authored trusted spec for EXT-025 contract_GP01 (terra_review r234 ACCEPT): headline statement(s) copied verbatim from Ext025HGP01 (QuantumNLS.Ext025HGP01). -/
noncomputable section
set_option autoImplicit false
open Set Topology
namespace QuantumNLS.X25GP01Spec
open QuantumNLS.Ext025HGP01


set_option maxHeartbeats 8000000 in
theorem contract_GP01_spec {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (A : Subalgebra ℂ C(K, ℂ))
    (hstar : ∀ f ∈ A, star f ∈ A)
    (hsep : A.SeparatesPoints) :
    Dense (A : Set C(K, ℂ)) := by
  exact QuantumNLS.Ext025HGP01.contract_GP01 A hstar hsep

end QuantumNLS.X25GP01Spec
#print axioms QuantumNLS.X25GP01Spec.contract_GP01_spec

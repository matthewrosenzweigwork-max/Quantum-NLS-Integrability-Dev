import QuantumNLS.Ext025LGP07Root
/-! integrator-authored trusted spec for EXT-025 contract_GP07_unconditional (contract ACCEPT): headline statement(s) copied verbatim from Ext025LGP07Root (QuantumNLS.Ext025L). -/
set_option autoImplicit false
universe u
universe u'
set_option maxHeartbeats 3200000
noncomputable section
open Filter Topology
open scoped InnerProductSpace LinearPMap
namespace QuantumNLS.X25GP07Spec
open QuantumNLS.Ext025L
open QuantumNLS.Ext025B7ClosedForm
open QuantumNLS.Ext025L.Polar
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (F : FormData E)

set_option maxHeartbeats 8000000 in
theorem contract_GP07_unconditional_spec {E : Type u'} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (F : QuantumNLS.Ext025B7ClosedForm.FormData E) :
    ∃ T : E →ₗ.[ℂ] E,
      (IsSelfAdjoint T ∧
        ∀ x f : E, (∃ hx : x ∈ T.domain, T ⟨x, hx⟩ = f) ↔
          ∃ hx : x ∈ F.domain, ∀ v : F.domain, F.q v ⟨x, hx⟩ = ⟪(v : E), f⟫_ℂ) ∧
      (∀ T' : E →ₗ.[ℂ] E, GP07_prop F T' → T' = T) ∧ GP07_formdomain F T ∧
      GP07_root_prop F T (formRoot F) := by
  exact QuantumNLS.Ext025L.contract_GP07_unconditional F

end QuantumNLS.X25GP07Spec
#print axioms QuantumNLS.X25GP07Spec.contract_GP07_unconditional_spec

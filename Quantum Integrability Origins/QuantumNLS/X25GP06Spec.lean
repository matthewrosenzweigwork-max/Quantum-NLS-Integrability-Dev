import QuantumNLS.Ext025AFoundations
/-! integrator-authored trusted spec for EXT-025 GP-06 (review record r1 ACCEPT): headline statement(s) copied verbatim from Ext025AFoundations (QuantumNLS.Ext025A). -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology InnerProductSpace WeakDual
open scoped ComplexConjugate
namespace QuantumNLS.X25GP06Spec
open QuantumNLS.Ext025A


set_option maxHeartbeats 8000000 in
theorem FIN_EXT025_GP_06_spec {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (ℓ : E →L[𝕜] 𝕜) :
    (∃! v : E, ∀ w : E, inner 𝕜 v w = ℓ w) ∧
      ‖(toDual 𝕜 E).symm ℓ‖ = ‖ℓ‖ := by
  exact QuantumNLS.Ext025A.«FIN-EXT025-GP-06» ℓ

end QuantumNLS.X25GP06Spec
#print axioms QuantumNLS.X25GP06Spec.FIN_EXT025_GP_06_spec

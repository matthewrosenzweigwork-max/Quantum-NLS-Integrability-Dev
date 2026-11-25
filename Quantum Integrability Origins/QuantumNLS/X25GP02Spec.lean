import QuantumNLS.Ext025AFoundations
/-! integrator-authored trusted spec for EXT-025 GP-02 (review record r1 ACCEPT): headline statement(s) copied verbatim from Ext025AFoundations (QuantumNLS.Ext025A). -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology InnerProductSpace WeakDual
open scoped ComplexConjugate
namespace QuantumNLS.X25GP02Spec
open QuantumNLS.Ext025A


set_option maxHeartbeats 8000000 in
theorem FIN_EXT025_GP_02_spec (A : Type*) [CommCStarAlgebra A] [Nontrivial A] :
    ∃ e : A ≃⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ),
      Isometry e ∧ ∀ a χ, e a χ = χ a := by
  exact QuantumNLS.Ext025A.«FIN-EXT025-GP-02» A

end QuantumNLS.X25GP02Spec
#print axioms QuantumNLS.X25GP02Spec.FIN_EXT025_GP_02_spec

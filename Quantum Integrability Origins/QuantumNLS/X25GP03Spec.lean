import QuantumNLS.Ext025LGP03CxMain
/-! integrator-authored trusted spec for EXT-025 GP-03 (review record r79 ACCEPT): headline statement(s) copied verbatim from Ext025LGP03CxMain (QuantumNLS.Ext025GP03Cx). -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace QuantumNLS.X25GP03Spec
universe u1 u2 u3 v1 v2 v3
open QuantumNLS.Ext025GP03Cx
open QuantumNLS.Ext025L

set_option maxHeartbeats 8000000 in
theorem contract_GP03_fixed_spec :
    GP03_A.{u1, u2} ∧ GP03_B.{u1, u2, u3} ∧ GP03_C_gen.{u1, u2, v1, v2} ∧
      GP03_D_gen.{v1, v2, v3} ∧ GP03_E_gen.{u1, u2, u3, v1, v2, v3} := by
  exact QuantumNLS.Ext025GP03Cx.contract_GP03_fixed 

end QuantumNLS.X25GP03Spec
#print axioms QuantumNLS.X25GP03Spec.contract_GP03_fixed_spec

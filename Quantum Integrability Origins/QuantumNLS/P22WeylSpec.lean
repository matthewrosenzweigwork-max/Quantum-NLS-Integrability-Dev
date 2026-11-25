import QuantumNLS.Prop022CWeyl
/-! integrator-authored trusted spec for PROP-022 intrinsic (Prop022CWeyl): headline statement(s) copied verbatim from Prop022CWeyl (QuantumNLS.Prop022CWeyl). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace Topology
open Filter
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.P22WeylSpec
open QuantumNLS.Prop022CWeyl
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022AIsoTensor
open QuantumNLS.Prop022BIso QuantumNLS.Prop022CCanon QuantumNLS.Prop022BFock1
open QuantumNLS.Prop022CStone QuantumNLS.Prop022CTorus QuantumNLS.Prop022BFock2
open PhysicalTensor Ext025B3PhysicalSectors
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem unitary_printedWeyl_eq_intrinsic_spec (U : H ≃ₗᵢ[ℂ] L2T L) (v : H)
    (W : FockSpace H ≃ₗᵢ[ℂ] FockSpace H) (hW : IsWeylOp v W) (x : FockSpace H) :
    (Prop022AFock.gam U).symm
      (Prop022OVacuum.printedWeyl (U v) (Prop022AFock.gam U x)) = W x := by
  first
  | exact QuantumNLS.Prop022CWeyl.unitary_printedWeyl_eq_intrinsic
  | (apply QuantumNLS.Prop022CWeyl.unitary_printedWeyl_eq_intrinsic <;> assumption)

set_option maxHeartbeats 8000000 in
theorem isometry_printedWeyl_eq_intrinsic_spec (J : H →ₗᵢ[ℂ] L2T L) (v : H)
    (W : FockSpace H ≃ₗᵢ[ℂ] FockSpace H) (hW : IsWeylOp v W) (x : FockSpace H) :
    gamAdj J (Prop022OVacuum.printedWeyl (J v) (fockMapI J x)) = W x := by
  first
  | exact QuantumNLS.Prop022CWeyl.isometry_printedWeyl_eq_intrinsic
  | (apply QuantumNLS.Prop022CWeyl.isometry_printedWeyl_eq_intrinsic <;> assumption)

end QuantumNLS.P22WeylSpec
#print axioms QuantumNLS.P22WeylSpec.unitary_printedWeyl_eq_intrinsic_spec
#print axioms QuantumNLS.P22WeylSpec.isometry_printedWeyl_eq_intrinsic_spec

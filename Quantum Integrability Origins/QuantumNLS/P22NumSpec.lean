import QuantumNLS.Prop022DNumber
/-! integrator-authored trusted spec for PROP-022 intrinsic (Prop022DNumber): headline statement(s) copied verbatim from Prop022DNumber (QuantumNLS.Prop022DNumber). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace ENNReal
open QuantumNLS.TensorCarrier
namespace QuantumNLS.P22NumSpec
open QuantumNLS.Prop022DNumber
open QuantumNLS.Prop022GTensor QuantumNLS.Prop022CCanon QuantumNLS.Prop022CQuad
open QuantumNLS.TensorPlacements
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 8000000 in
theorem dGamma_one_eq_number_spec (x : FockSpace E) :
    dGammaSeq (ContinuousLinearMap.id ℂ (SymSector ℂ E 1)) x = numSeq x := by
  first
  | exact QuantumNLS.Prop022DNumber.dGamma_one_eq_number
  | (apply QuantumNLS.Prop022DNumber.dGamma_one_eq_number <;> assumption)

end QuantumNLS.P22NumSpec
#print axioms QuantumNLS.P22NumSpec.dGamma_one_eq_number_spec

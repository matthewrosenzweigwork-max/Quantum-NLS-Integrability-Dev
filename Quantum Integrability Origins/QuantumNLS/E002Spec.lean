import QuantumNLS.Ext002MonoMain
/-! integrator-authored trusted spec for EXT-002/V-01 full monodromy under D4 (review record r53 PASS): headline statement(s) copied verbatim from Ext002MonoMain (QuantumNLS.Ext002MonoMain). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace
namespace QuantumNLS.E002Spec
open QuantumNLS.Ext002MonoMain
open PhysicalTensor TensorCarrier BethePhysicalTransfer BetheTransferKernelAdjoint
open BetheTransferOperators Ext002MonoFields Ext002MonoEntries Ext002MonoSlice
open Ext002MonoCompression
variable (L : ℝ) [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem v01_gauged_trace_eq_transfer_spec (N : ℕ) (c : ℝ) (z : ℂ) :
    Complex.exp (Complex.I * z * L / 2) • (monodromy L N c z).trace =
      BethePhysicalTransfer.transfer L N c z := by
  exact QuantumNLS.Ext002MonoMain.v01_gauged_trace_eq_transfer L N c z

end QuantumNLS.E002Spec
#print axioms QuantumNLS.E002Spec.v01_gauged_trace_eq_transfer_spec

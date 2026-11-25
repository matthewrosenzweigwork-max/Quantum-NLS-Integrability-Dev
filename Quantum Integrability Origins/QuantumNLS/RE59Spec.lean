import QuantumNLS.Bind7BE59628C9H01
/-! integrator-authored trusted spec for R-E59628C9 prop:window (hierarchy-bound): headline statement(s) copied verbatim from Bind7BE59628C9H01 (QuantumNLS.Bind7BE59628C9H01). -/
set_option autoImplicit false
namespace QuantumNLS.RE59Spec
open QuantumNLS.Bind7BE59628C9H01
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem window_bound_spec (hκ : 0 < κ) : QuantumNLS.Prop025OInputs.WindowInput (L := L) hκ := by
  first
  | exact QuantumNLS.Bind7BE59628C9H01.window_bound
  | (apply QuantumNLS.Bind7BE59628C9H01.window_bound <;> assumption)

end QuantumNLS.RE59Spec
#print axioms QuantumNLS.RE59Spec.window_bound_spec

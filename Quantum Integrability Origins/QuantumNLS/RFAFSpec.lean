import QuantumNLS.ReconstructionFinalR35m
/-! integrator-authored trusted spec for R-FAF88C8A thm:reconstruction (final): headline statement(s) copied verbatim from ReconstructionFinalR35m (QuantumNLS.ReconstructionFinalR35m). -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace QuantumNLS.RFAFSpec
open QuantumNLS.ReconstructionFinalR35m
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem reconstruction_spec (hκ : 0 < κ) :
    ReconstructionR33m.Reconstruction hκ
      (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))
      (DynamicGaugeFinalR35m.gauge (L := L) hκ) := by
  first
  | exact QuantumNLS.ReconstructionFinalR35m.reconstruction
  | (apply QuantumNLS.ReconstructionFinalR35m.reconstruction <;> assumption)

end QuantumNLS.RFAFSpec
#print axioms QuantumNLS.RFAFSpec.reconstruction_spec

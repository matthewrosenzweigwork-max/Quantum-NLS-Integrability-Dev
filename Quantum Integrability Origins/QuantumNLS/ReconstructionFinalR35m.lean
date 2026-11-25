import QuantumNLS.ReconstructionR33m
import QuantumNLS.DynamicGaugeFinalR35m
import QuantumNLS.RB7BindFinal

/-! Final binding of R-FAF88C8A at the R-8362E5EB gauge. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace QuantumNLS.ReconstructionFinalR35m

variable {L κ : ℝ} [Fact (0 < L)]

/-- R-FAF88C8A, printed as thm:reconstruction. Uniform trace-norm
reconstruction uses the actual hierarchy and the same named gauge as the
strong Cartesian comparison. -/
theorem reconstruction (hκ : 0 < κ) :
    ReconstructionR33m.Reconstruction hκ
      (ReconstructionR33m.flows hκ (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))
      (DynamicGaugeFinalR35m.gauge (L := L) hκ) :=
  ReconstructionR33m.reconstruction_ofInput hκ (DynamicGaugeFinalR35m.gauge (L := L) hκ)
    (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ)
    (DynamicGaugeFinalR35m.audit_dynamic_gauge (L := L) hκ)

end QuantumNLS.ReconstructionFinalR35m

#print axioms QuantumNLS.ReconstructionFinalR35m.reconstruction

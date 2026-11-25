import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5

/- KSPS-003 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS003Host.lean.
   The two bodies are copied from Pro round 6 (c5547100) section 10A / DEFINITIONS/KSPS.lean.md lines 118-120 and
   186-192 (identical in rounds 5, 6 and 10); they are absent from production. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def sobolevNorm (N : ℕ) (φ : SobolevC N) : ℝ :=
  Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2)

def secondVolterraRemainder (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  volterraTerm 2 x lam φ -
    (2 * lam)⁻¹ •
      (freePropagator x lam *
        NlsGge.ThirdConsultation.KSPSVolterra.R *
        NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ x)

end
end NlsGge.ThirdConsultation.KSPS

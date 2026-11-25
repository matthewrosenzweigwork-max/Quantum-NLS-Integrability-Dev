import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5

/- KSPS-005 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS005Host.lean.
   The two bodies are copied verbatim from DEFINITIONS/KSPS.lean.md (lines 121-122 and 194-200; identical in
   rounds 5, 6, 9, 10, 11); they are absent from production (Round5 and KSPS003Host do not define them).
   `fundamentalRemainderMajorant` and `inverseFundamentalRemainder` (KSPS-006) are deliberately NOT hosted here. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def l2Norm {N : ℕ} (φ : SobolevC N) : ℝ :=
  Real.sqrt (‖(toPotPair φ).1‖^2 + ‖(toPotPair φ).2‖^2)

def fundamentalRemainder (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :=
  NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ x lam -
    freePropagator x lam - volterraTerm 1 x lam φ -
    (2*lam)⁻¹ •
      (freePropagator x lam *
        NlsGge.ThirdConsultation.KSPSVolterra.R *
        NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ x)

end
end NlsGge.ThirdConsultation.KSPS

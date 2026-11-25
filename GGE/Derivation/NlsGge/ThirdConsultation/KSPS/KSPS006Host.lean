import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPS.KSPS005Host

/- KSPS-006 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS006Host.lean.
   The two bodies are copied from DEFINITIONS/KSPS.lean.md (followup9 tree, lines 202-204 and 206-212; identical in
   rounds 5, 6, 9, 10, 11); they are absent from NlsGge/ (grep). Only lexical repair: `|lam.im|*x` -> `|lam.im| * x`
   (the token `|*` does not lex, cf. KSPS-005). `l2Norm` and `fundamentalRemainder` are REUSED from KSPS005Host. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def fundamentalRemainderMajorant (φ : SobolevC 1) (x : ℝ) (lam : ℂ) : ℝ :=
  Real.exp (|lam.im| * x + l2Norm φ) *
    sobolevNorm 1 φ^2 * (1+sobolevNorm 1 φ) / ‖lam‖^2

def inverseFundamentalRemainder (φ : SobolevC 1) (x : ℝ) (lam : ℂ) :=
  NlsGge.ThirdConsultation.KSPSVolterra.inverseFundamental φ x lam -
    freePropagator (-x) lam + volterraTerm 1 x lam φ +
    (2*lam)⁻¹ •
      (freePropagator (-x) lam *
        NlsGge.ThirdConsultation.KSPSVolterra.R *
        NlsGge.ThirdConsultation.KSPSVolterra.integratedQuadratic φ x)

end
end NlsGge.ThirdConsultation.KSPS

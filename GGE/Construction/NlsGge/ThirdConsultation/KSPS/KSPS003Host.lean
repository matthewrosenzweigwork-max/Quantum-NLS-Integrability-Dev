import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5

                                                                                                              
                                                                                                                 
                                                                                 
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

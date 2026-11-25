import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5

                                                                                                              
                                                                                                            
                                                                                                        
                                                                                                                   
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

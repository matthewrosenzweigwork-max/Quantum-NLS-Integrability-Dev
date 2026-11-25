import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPS.KSPS005Host

                                                                                                              
                                                                                                                   
                                                                                                                    
                                                                                                                   
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

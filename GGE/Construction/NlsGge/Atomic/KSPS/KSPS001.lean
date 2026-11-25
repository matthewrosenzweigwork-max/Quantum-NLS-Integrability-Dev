import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5

                                                                                                                                                                                                             
set_option autoImplicit false

open NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem wkb_fourier_derivative (N : ℕ) (φ : SobolevC N) (n : ℤ) :
  physicalFourier (iteratedDerivative N φ.1) n =
    (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N *
      physicalFourier (toPotPair φ).1 n ∧
  physicalFourier (iteratedDerivative N φ.2) n =
    (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ N *
      physicalFourier (toPotPair φ).2 n :=
  ⟨NlsGge.GKDefinitionDesign.physicalSobolevDerivative38_fourier N φ.1 n,
   NlsGge.GKDefinitionDesign.physicalSobolevDerivative38_fourier N φ.2 n⟩

end
end NlsGge.ThirdConsultation.KSPS

import Mathlib
import NlsGge.Schur.FreeResolventComplementarySquareBoundAfterQDTransport

                                                                          
                                                                                                
                                                                           
set_option autoImplicit false

open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur

namespace NlsGge.ThirdConsultation.S
noncomputable section

def interaction (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) :
    ParityPair n →L[ℂ] ParityPair n :=
  freeResolventComplementaryPotentialA u₁ u₂ hu₁ hu₂ n z hz

def complementaryInteractionConstant : ℝ :=
  1 + 2 * physicalH1MultiplierConstant +
    4 * freeResolventSchurUniformConstant * physicalH1MultiplierConstant

def rankOneProj
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : H) : H →L[ℂ] H :=
  (innerSL ℂ e).smulRight e

end
end NlsGge.ThirdConsultation.S

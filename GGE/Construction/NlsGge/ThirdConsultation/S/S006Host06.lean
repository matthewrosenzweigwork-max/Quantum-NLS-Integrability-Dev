import Mathlib
import NlsGge.Atomic.S.S009
import NlsGge.ThirdConsultation.S.Round4
import NlsGge.Schur.FreeResolventComplementaryQDTransportAfterCoordinateRange

                                                                                                      
                                                                                                                  
                                                                                     
                                                                                                                      
                                                                                                                                   
set_option autoImplicit false

open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S
noncomputable section

def basisPlus (n : ℤ) : ParityPair n :=
  parityPairVector n (true, resonantIndex n)

def oppositeInteraction (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂)) :
    ParityPair n →L[ℂ] ParityPair n :=
  (freeResolventComplementaryProjectionTransported n).comp
    ((schurV u₁ u₂ hu₁ hu₂ n).comp (schurD n z hz))

def complementaryResolvent
    (R : ℝ) (hR : 1 ≤ R)
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (hpair : schurPairH1Norm u₁ u₂ hu₁ hu₂ ≤ R)
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n)
    (hlarge : complementaryInteractionConstant * R ^ 2 ≤ |(n : ℝ)|) :
    ParityPair n →L[ℂ] ParityPair n :=
  (Ring.inverse (1 - interaction n z hz u₁ u₂ hu₁ hu₂)).comp
    (schurD n z hz)

end
end NlsGge.ThirdConsultation.S

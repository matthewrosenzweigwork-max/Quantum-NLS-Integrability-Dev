import Mathlib
import NlsGge.ThirdConsultation.KST.KST066Host
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.ThirdConsultation.Sobolev.Round5

                                                                                            
                                                                                                                   
                                                                                                  
                                                                                                                         
                                                                                                                       
                                                                                                               
                                                                                                               
                                                                                                              
                                                                                           
set_option autoImplicit false
noncomputable section
open scoped Classical
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

def physicalSobolevRecoverRealExponent (s : ℝ) (u : PhysicalL2) : PhysicalSobolev38 s :=
  if h : fourierSeq38 u ∈ seqSobolev38 s then
    (physicalSobolevFourierEquiv38 s).symm (carrierMk38 s (fourierSeq38 u) h)
  else 0

def inverseBirkhoffSobolevRealExponent (s : ℝ) (hs : 0 ≤ s) (z : SobolevCarrier38 s) :
    PhysicalSobolev38 s :=
  physicalSobolevRecoverRealExponent s
    (physicalInverseBirkhoff (sequenceSobolevEmbedRealExponent s hs z))

def inverseSmoothing (N : ℕ) (z : SobolevCarrier38 (N : ℝ)) :
    PhysicalSobolev38 ((N : ℝ) + 1) :=
  physicalSobolevRecoverRealExponent ((N : ℝ) + 1)
    (physicalInverseBirkhoff (sequenceSobolevEmbed N z) -
      reflectedFourierL2.symm (sequenceSobolevEmbed N z))

end NlsGge.GKDefinitionDesign

end

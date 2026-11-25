import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.GK38.Lib.InterpolationHilbertOp
import NlsGge.Sobolev.PeriodicBridge

                                                                                                                    
                                                                                                                   
                                                                                                                               
                                                                                                           
                                                                                                                              
                                                                               
set_option autoImplicit false
noncomputable section

namespace NlsGge.GKDefinitionDesign
open NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common
open NlsGge.Pilot NlsGge.GK38

def sequenceSobolevEmbedRealExponent (s : ℝ) (hs : 0 ≤ s)
    (z : SobolevCarrier38 s) : Lib.L2Z :=
  let z0 := carrierIncl38 (r := 0) (s := s) hs z
  seqToLp38 (carrierCoe38 0 z0) (carrierCoe38_mem 0 z0)

def physicalSobolevEmbedRealExponent (s : ℝ) (hs : 0 ≤ s)
    (u : PhysicalSobolev38 s) : PhysicalL2 :=
  reflectedFourierL2.symm (sequenceSobolevEmbedRealExponent s hs
    (physicalSobolevFourierEquiv38 s u))

end NlsGge.GKDefinitionDesign
end

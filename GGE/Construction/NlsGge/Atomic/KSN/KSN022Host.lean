import NlsGge.ThirdConsultation.KST.KST066Host
import NlsGge.ThirdConsultation.G6.BirkhoffBasic

                                                                            
                                                                                           
                                                                                                    
                                                                                   
                                                                                                           
                                                                                                                     
                                                                                       
                                                                                                               
                                                                                                             
                                                                                                           
set_option autoImplicit false
noncomputable section
open scoped Classical
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

def birkhoffSobolevRealExponent (s : ℝ) (hs : 0 ≤ s) (u : PhysicalSobolev38 s) :
    SobolevCarrier38 s :=
  let z : ℤ → ℂ := physicalBirkhoff (physicalSobolevEmbedRealExponent s hs u)
  if h : z ∈ seqSobolev38 s then carrierMk38 s z h else 0

end NlsGge.GKDefinitionDesign

end

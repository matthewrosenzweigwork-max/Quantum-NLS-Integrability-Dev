import Mathlib
import NlsGge.Atomic.G2.G2046

                                                                                               
                                                                                                  
                                                                                                                         
                                                                                                                  
                                                                                                             
                                                                                                              
set_option autoImplicit false
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

def finiteGapPair (φ : PotPair) : Prop :=
  {n : ℤ | NlsGge.GKDefinitionDesign.gap φ n ≠ 0}.Finite

end NlsGge.ThirdConsultation.M

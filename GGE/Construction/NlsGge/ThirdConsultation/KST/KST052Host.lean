import Mathlib
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.KST.KST013

                                                                                                                          
                                                                                                       
                                                                                                              
                                                                                                                   
                                                                                                                     
                                                                          
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST013

namespace NlsGge.ThirdConsultation.KST

def eigenspace (φ : Potential) (z : ℂ) : Submodule ℂ (dirac φ).domain :=
  LinearMap.ker ((dirac φ).toFun - z • (dirac φ).domain.subtype)

end NlsGge.ThirdConsultation.KST
end

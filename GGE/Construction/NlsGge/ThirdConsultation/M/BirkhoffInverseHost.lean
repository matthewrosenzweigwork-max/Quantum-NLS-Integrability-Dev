import Mathlib
import NlsGge.Atomic.M.M005
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff

                                                                                                                                    
                                                                                                                 
                                                                                                                    
                                                                                                                      
                                                                                                              
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M
noncomputable section

abbrev RealSobolevSequence (m : ℕ) := NlsGge.Sobolev38.SobolevCarrier38 (m:ℝ)

def birkhoffInverse (m : ℕ) (z : RealSobolevSequence m) : SobolevR m :=
  NlsGge.GKDefinitionDesign.inverseBirkhoffSobolev m z

end
end NlsGge.ThirdConsultation.M

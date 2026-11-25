import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38

                                                                                                              
                                                                                             
                                                                                                                      
                                                                                                                        
                                                                                                                 
                                                                                                                
                                                                                                               
set_option autoImplicit false
open NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def closedGap (u : SobolevR 1) (n : ℤ) : Set ℝ :=
  Set.Icc
    (actualGapLowerAllE02_38 (toPhysical u) n)
    (actualGapUpperAllE02_38 (toPhysical u) n)

end
end NlsGge.ThirdConsultation.KSPS

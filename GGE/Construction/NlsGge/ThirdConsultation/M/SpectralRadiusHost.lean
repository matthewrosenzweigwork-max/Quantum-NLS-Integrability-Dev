import Mathlib
import NlsGge.ThirdConsultation.M.M033Host

                                                                                  
                                                                                                     
                                                                                                                
                                                                                              
                                                                                                                  
                                                                                                    
set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.MEstimates

def spectralRadius (u : M.SobolevR 1) : ℝ :=
  8 * Real.pi * MTwoMode.H1Norm u ^ 2

end NlsGge.ThirdConsultation.MEstimates

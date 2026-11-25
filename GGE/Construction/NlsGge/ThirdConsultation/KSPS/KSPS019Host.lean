import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.PeriodicLabellingCanonical

                                                                                                              
                                                                                                                       
                                                                                                                             
                                                                                                                         
                                                                                                                             
                                                                                                                        
                                                                                                    
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def mu {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  NlsGge.GK38.muSeq (toPotPair φ) n

def criticalEigenvalue {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  NlsGge.GK38.lamDot (toPotPair φ) n

end
end NlsGge.ThirdConsultation.KSPS

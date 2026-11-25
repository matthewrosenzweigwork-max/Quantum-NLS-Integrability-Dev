import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.GK38.PeriodicLabellingCanonical

                                                                                                              
                                                                                                                            
                                                                                                                  
                                                                                                                    
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def periodicMinus {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  NlsGge.GK38.lamMinus (toPotPair φ) n

def periodicPlus {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  NlsGge.GK38.lamPlus (toPotPair φ) n

end
end NlsGge.ThirdConsultation.KSPS

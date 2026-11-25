import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS020Host
import NlsGge.ThirdConsultation.KSPS.KSPS023Host

                                                                                                              
                                                                                                                 
                                                                                                               
                                                                                                                     
                                                                                                       
                                                                                                                                                                                      
                
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common NlsGge.ThirdConsultation
open NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def midpoint {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  (periodicMinus φ n + periodicPlus φ n) / 2

end
end NlsGge.ThirdConsultation.KSPS

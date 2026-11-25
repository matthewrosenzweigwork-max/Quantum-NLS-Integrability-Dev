import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS015Host
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

def LpSequence (p : ℝ) (e : ℤ → ℂ) : Prop :=
  Summable (fun n : ℤ => ‖e n‖^p)

end
end NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def WeightedSquareSummable (s : ℝ) (e : ℤ → ℂ) : Prop :=
  WeightedL2Error s e

end
end NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def gap {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  periodicPlus φ n - periodicMinus φ n

end
end NlsGge.ThirdConsultation.KSPS

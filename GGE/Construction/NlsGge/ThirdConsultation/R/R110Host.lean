import Mathlib
import NlsGge.ThirdConsultation.R.R109Host

                                                                                                                        
                                                                                                           
                                                                                                                   
                                                                                                                       
                                                                                                                 
                            
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer

namespace NlsGge.ThirdConsultation.R
noncomputable section

def actualRamerDensity {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) : ECarrier38 c s → ℝ :=
  NlsGge.Birkhoff.fW06_38 c s hs (weightedK c s hs1)
    (canonicalDelta c s hs hs1)

end
end NlsGge.ThirdConsultation.R

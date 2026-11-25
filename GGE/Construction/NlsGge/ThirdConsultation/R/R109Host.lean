import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.ThirdConsultation.R.R100Host

                                                                                                                                       
                                                                                                                   
                                                                                                                
                                                                                                                              
                                                                                                                      
                                                                                                                    
                                                           
                                                                                                                
                                                                                                                            
                                                                                                                          
                                                                                                           
                                                                                                                       
                                                                                                                   
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- Choice from the already proved Ramer theorem, before W07/W11 is used. -/
noncomputable def canonicalDelta {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) : (ℤ → ℂ) → ℝ :=
  Classical.choose (NlsGge.Birkhoff.ramer_W06_38 PDE.actualBirkhoffInput38
    PDE.actualOneSmoothingInput38 c s hs hs1)

theorem canonicalDelta_spec {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) :
    NlsGge.Birkhoff.RamerDivergence38 c s
      (PDE.actualBirkhoffInput38.KW06_38 PDE.actualOneSmoothingInput38 c hs1)
      (canonicalDelta c s hs hs1)
 :=
  (Classical.choose_spec (NlsGge.Birkhoff.ramer_W06_38 PDE.actualBirkhoffInput38
    PDE.actualOneSmoothingInput38 c s hs hs1)).1


def actualRamerJac {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) : ECarrier38 c s → ℝ :=
  NlsGge.Birkhoff.JW06_38 c s hs (weightedK c s hs1)
    (canonicalDelta c s hs hs1)

end
end NlsGge.ThirdConsultation.R

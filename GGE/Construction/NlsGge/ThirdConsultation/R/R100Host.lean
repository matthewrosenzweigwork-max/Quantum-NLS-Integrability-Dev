import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52

                                                                                                                        
                                                                                                               
                                                                                                                  
                                                                                                                      
                                                                                                                       
                                                                                                             
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer

namespace NlsGge.ThirdConsultation.R
noncomputable section

def weightedK {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (hs1 : s ≤ 1) : ECarrier38 c s → ActualCM c :=
  PDE.actualBirkhoffInput38.KW06_38 PDE.actualOneSmoothingInput38 c hs1

def Kinv {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (hs1 : s ≤ 1) : ECarrier38 c s → ActualCM c :=
  PDE.actualBirkhoffInput38.KinvW06_38 PDE.actualOneSmoothingInput38 c hs1

end
end NlsGge.ThirdConsultation.R

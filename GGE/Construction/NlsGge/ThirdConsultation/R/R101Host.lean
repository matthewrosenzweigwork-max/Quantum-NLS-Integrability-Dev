import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52

                                                                                                                        
                                                                                                                       
                                                                                                                     
                                                                                                                     
                                                                                
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- The actual E_s homeomorphism, without any artificial s-window on this deterministic map. -/
def actualWeightedBirkhoffHomeo {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) :
    ECarrier38 c s ≃ₜ ECarrier38 c s :=
  PDE.actualBirkhoffInput38.weightedHomeoE38 PDE.actualOneSmoothingInput38 c s

end
end NlsGge.ThirdConsultation.R

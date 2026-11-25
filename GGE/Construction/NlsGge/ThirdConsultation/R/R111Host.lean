import Mathlib
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52

                                                                                                                        
                                                                                                                 
                                                                                                                  
                                                                                                                      
                            
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- Same literal Gaussian pushforward as gammaF_eq_W06_38. -/
def actualFourierGaussian {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) : Measure PhysicalL2 :=
  (fullWeightedSequenceGaussian c s).map (physFW06_38 c s)

end
end NlsGge.ThirdConsultation.R

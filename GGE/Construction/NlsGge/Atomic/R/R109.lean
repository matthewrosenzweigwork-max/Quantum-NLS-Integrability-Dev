import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.ThirdConsultation.R.R100Host
import NlsGge.ThirdConsultation.R.R101Host
import NlsGge.ThirdConsultation.R.R109Host
import NlsGge.ThirdConsultation.T.ECarrier98

                                                                                                                      
                                                                                                                      
                                                                                                                 
                                                                                                                          
                                                                                                                                                                                                          
                                                                                                          
                                                                                                                 
                                                                              
                                                                                                                           
                                                                                                                                                  
                                                                                                                 
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem canonicalDelta_characterization {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) :
    RamerDivergence38 c s (weightedK c s hs1) (canonicalDelta c s hs hs1) ∧
    (fullWeightedSequenceGaussian c s).map (actualWeightedBirkhoffHomeo c s).symm =
      (fullWeightedSequenceGaussian c s).withDensity
        (fun x : ECarrier38 c s => ENNReal.ofReal (actualRamerJac c s hs hs1 x)) ∧
    (∀ x : ECarrier38 c s, 0 < actualRamerJac c s hs hs1 x) ∧
    Integrable (actualRamerJac c s hs hs1) (fullWeightedSequenceGaussian c s) ∧
    (∫ x : ECarrier38 c s, actualRamerJac c s hs hs1 x
      ∂(fullWeightedSequenceGaussian c s)) = 1 :=
  Classical.choose_spec (NlsGge.Birkhoff.ramer_W06_38 PDE.actualBirkhoffInput38
    PDE.actualOneSmoothingInput38 c s hs hs1)

end NlsGge.ThirdConsultation.R

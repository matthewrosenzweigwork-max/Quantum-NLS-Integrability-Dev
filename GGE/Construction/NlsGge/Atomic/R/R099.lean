import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

                                                                                                  
                                                                                                               
                                                                                                       
                                                                                                                    
                                                                                                                                                                             
                                                                                                      
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r099_main {lower upper : ℝ}  
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    AnalyticOnNhd ℝ ((B).weightedHomeoE38 O c s).symm Set.univ :=
  BirkhoffInput38.analytic_weightedHomeoE38_symm B O c s

end NlsGge.ThirdConsultation.R

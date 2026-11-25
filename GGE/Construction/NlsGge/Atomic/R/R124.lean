import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W09Approx38b
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

theorem r124_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (x : ECarrier38 c s) :
    Tendsto (fun N : ℕ => ‖fderiv ℝ ((B).KE38 O c s) x -
      (projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) x)‖) atTop (𝓝 0) :=
  (B).tendsto_tail_DKE38 O c s x

end NlsGge.ThirdConsultation.R

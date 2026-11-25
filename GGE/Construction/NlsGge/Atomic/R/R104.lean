import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W05FiniteGap38
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

theorem r104_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)  (hs : s < 3 / 4) :
    Continuous (fun x : ECarrier38 c s => remainder38 c.val (physOfE38 c s x)) :=
  BirkhoffInput38.continuous_remainder_physOfE38 B c s O hs

end NlsGge.ThirdConsultation.R

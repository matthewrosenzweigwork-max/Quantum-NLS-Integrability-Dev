import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.F01Determinant38c
import NlsGge.Ramer.RamerFiniteChainRule

                                                                                                              
                                                                                                                 
                                                                                            
                                                                                                                                 
                                                                                                 
                                                                                           
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r064_main : Continuous ((B).BHS O) :=
  NlsGge.Birkhoff.BirkhoffInput38.continuous_BHS B O

end NlsGge.ThirdConsultation.R

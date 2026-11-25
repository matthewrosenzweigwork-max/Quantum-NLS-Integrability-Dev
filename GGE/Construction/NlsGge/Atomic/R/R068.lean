import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.F01Determinant38d
import NlsGge.Ramer.RamerFiniteChainRule

                                                                                                              
                                                                                                                 
                                                                                                        
                                                                                                                                       
                                                                                                                  
                                                     
                                                                                                                      
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r068_main (x : H1_38) (N : ℕ) :
    |(B).detMN x N - 1| ≤ detErr38 (‖(B).cHS O x N‖ ^ 2) :=
  NlsGge.Birkhoff.BirkhoffInput38.abs_detMN_sub_one_le B O x N

end NlsGge.ThirdConsultation.R

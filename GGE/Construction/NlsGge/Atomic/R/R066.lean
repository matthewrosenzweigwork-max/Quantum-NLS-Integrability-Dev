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

theorem r066_main {K : Set H1_38} (hK : IsCompact K) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ x ∈ K, ‖(B).cHS O x N‖ < ε :=
  NlsGge.Birkhoff.BirkhoffInput38.eventually_norm_cHS_lt B O hK

end NlsGge.ThirdConsultation.R

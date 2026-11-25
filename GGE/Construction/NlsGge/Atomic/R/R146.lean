import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W11Equivalence38e
import NlsGge.Ramer.RamerFiniteChainRule

                                                                                                              
                                                                                                                 
                                                                                        
                                                                                                             
                                                                                                                       
                                                                                                           
                                                                                                   
                                                                                                                   
                                                                                  
                                                                                                        
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r146_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (f : FullWeightedHilbert c s → ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) 
    (hW : W11Weight38 B c s f) (htight : W11Tight38 c) : W11Normalizer38 B c :=
  NlsGge.Birkhoff.BirkhoffInput38.normalizer_of_tight_W11 B O c hs hs' hW htight

end NlsGge.ThirdConsultation.R

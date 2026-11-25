import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W11Equivalence38d

                                                                                                              
                                                                                                               
                                                                                                                   
                                                                 
                                                                                                                    
                                                                                                
                                                                                               
                                                                                                       
                                                                                                  
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r144_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) (hweak : W11Weak38 B c s) :
    W11Tight38 c :=
  NlsGge.Birkhoff.BirkhoffInput38.tight_of_weak_W11 B O c hs hs' hweak

end NlsGge.ThirdConsultation.R

import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W10Localized38g
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

theorem r138_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) : 0 < ∫ u, chiR38 χ R u ∂((B).muW38 c.val) :=
  BirkhoffInput38.muW_chiR_pos38 B O c hs hs' hχ hR

end NlsGge.ThirdConsultation.R

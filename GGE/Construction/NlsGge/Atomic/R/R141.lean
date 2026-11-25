import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W11Equivalence38c
import NlsGge.Ramer.RamerFiniteChainRule

                                                                                                              
                                                                                                                 
                                                     
                                                  
                                                                                      
                                                                                                          
                                                                                                                       
                                                                                                                 
                                                                                                                         
                                                                                                          
                                                                                                                      
                                                                                                               
                                                                                  
                                                                                                        
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r141_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (f : FullWeightedHilbert c s → ℝ) (hs : (1 : ℝ) / 2 < s) (hW : W11Weight38 B c s f) :
    Tendsto (fun N : ℕ => relativePartition38 c N) atTop (𝓝 ((B).ZW38 c.val)) ↔
      Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x - f x| ∂(fullWeightedSequenceGaussian c s))
        atTop (𝓝 0) :=
  NlsGge.Birkhoff.BirkhoffInput38.tendsto_Z_iff_l1_W11 B c hs hW

end NlsGge.ThirdConsultation.R

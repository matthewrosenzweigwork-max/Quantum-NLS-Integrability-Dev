import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W05FiniteGap38
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

theorem remainder_nonneg_weighted {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) (hs : s < 3 / 4)
    (u : FinvE38 c s) : 0 ≤ remainder38 c.val u.1 :=
  (BirkhoffInput38.W05_38 B c s O hs).2.2.1 u

end NlsGge.ThirdConsultation.R

import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
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

theorem r118_main (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ballH1 R, ∀ y ∈ ballH1 R,
      ‖(B).Kfwd1 O x - (B).Kfwd1 O y‖ ≤ C * ‖x - y‖ :=
  (B).lipschitz_Kfwd1_ballH1 O R

end NlsGge.ThirdConsultation.R

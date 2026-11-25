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

theorem r119_main (R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ ballH1 R, ∀ y ∈ ballH1 R,
      ‖x - y‖ ≤ L * ‖(B).TC 1 x - (B).TC 1 y‖ :=
  (B).inverse_lipschitz_ballH1 O R

end NlsGge.ThirdConsultation.R

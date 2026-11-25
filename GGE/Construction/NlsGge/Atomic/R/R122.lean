import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Birkhoff.W08Compact38b
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

theorem r122_main  (R : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ x ∈ ballV38 N R, (B).detTN N x ≠ 0 ∧ |(B).detTN N x|⁻¹ ≤ 2 :=
  (B).eventually_inv_abs_detTN_le_two O R

end NlsGge.ThirdConsultation.R

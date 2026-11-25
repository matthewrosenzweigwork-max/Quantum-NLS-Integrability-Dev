import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.F01Determinant38c
import NlsGge.Birkhoff.W09Approx38b
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

theorem r130_main (R : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ζ : ℤ → ℂ, ∀ y w : H2_38, ‖y‖ ≤ R → ‖w‖ ≤ R →
      (B).GalerkinSol38 N ζ (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y) →
      (B).GalerkinSol38 N ζ (carrierCoe38 (((1 + 1 : ℕ)) : ℝ) w) →
      carrierCoe38 (((1 + 1 : ℕ)) : ℝ) y = carrierCoe38 (((1 + 1 : ℕ)) : ℝ) w :=
  (B).galerkinSol_unique_W09 O R

end NlsGge.ThirdConsultation.R

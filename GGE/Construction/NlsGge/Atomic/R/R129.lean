import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
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

theorem r129_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (z : ECarrier38 c s) :
    ∃ xN : ℕ → ECarrier38 c s,
      Tendsto xN atTop (𝓝 (((B).weightedHomeoE38 O c s).symm z)) ∧
      ∀ᶠ N in atTop, (B).GalerkinSol38 N (eCoe38 c s z) (eCoe38 c s (xN N)) :=
  (B).exists_galerkin_branch38 O c s z

end NlsGge.ThirdConsultation.R

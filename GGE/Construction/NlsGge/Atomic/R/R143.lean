import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Birkhoff.W11Equivalence38c
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

theorem r143_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (f : FullWeightedHilbert c s → ℝ) (hs : (1 : ℝ) / 2 < s) (hW : W11Weight38 B c s f)
    (hL1 : Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x - f x| ∂(fullWeightedSequenceGaussian c s))
      atTop (𝓝 0))
    (F : PhysicalL2 → ℝ) (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    Tendsto (fun N : ℕ => ∫ u, F u ∂(nuWN38 c N)) atTop (𝓝 (∫ u, F u ∂((B).muW38 c.val))) :=
  (B).weak_of_l1_W11 c hs hW hL1 F hF hFb

end NlsGge.ThirdConsultation.R

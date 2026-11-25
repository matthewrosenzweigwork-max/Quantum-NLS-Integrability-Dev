import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.ThirdConsultation.R.R109Host
import NlsGge.ThirdConsultation.R.R111Host

                                                                                                  
                                                                                                                   
                                                                                                                      
                                                                                                           
                                                                                                                      
                                                                                                              
                                                                                                                    
                                                                                                           
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem actual_mutually_absolutelyContinuous {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (B).muW38 c.val ≪ actualFourierGaussian c s ∧
      actualFourierGaussian c s ≪ (B).muW38 c.val := by
  have hs1 : s ≤ 1 := by linarith
  obtain ⟨-, hmap, hpos, hint, -⟩ := Classical.choose_spec
    (NlsGge.Birkhoff.ramer_W06_38 PDE.actualBirkhoffInput38 PDE.actualOneSmoothingInput38 c s hs hs1)
  exact (NlsGge.Birkhoff.density_W06_38 PDE.actualBirkhoffInput38 c s
    PDE.actualOneSmoothingInput38 hs hs' _ hmap hint hpos).2.2.2.2.2

end NlsGge.ThirdConsultation.R

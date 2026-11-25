import Mathlib
import NlsGge.Atomic.G5.G5029Sup4Core
import NlsGge.Atomic.G5.G5020
import NlsGge.Atomic.G4.G4041

                                                                           
                                                                               
                                                                                                                                   
                                                                                                                                             
                                                                                                                                  
                                                                                                                                                     
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem continuousOn_angleIntegralBracket
    (k l m n : ℤ) :
  ContinuousOn
    (fun u : PhysicalL2 =>
      pairPoissonCLM (angleIntegralDerivative k m (realSlice u))
        (angleIntegralDerivative l n (realSlice u)))
    {u : PhysicalL2 | gamma2 (realSlice u) m ≠ 0 ∧
      gamma2 (realSlice u) n ≠ 0} :=
  G5029Sup4Aux.continuousOn_bracket_core k l m n G4041 betaSum_analyticOnNhd_sourceBetaW
    G5020Aux.term_analytic

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import Armstrong.Work.RawBetaSum

                                                                              
                                                     
                                                                                                        
                                                                                                                                       
                                                                                                                              
                                                                                                                                     
                                                                                                             
                                                                                                            
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def offDiagonalBeta (n m : ℤ) : PotPair → ℂ :=
  gk151BetaAmbient38 sourceW sourceFamily.W_open sourceFamily.W_real
    sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
    sourceFamily.F_period n m

end
end NlsGge.GKDefinitionDesign

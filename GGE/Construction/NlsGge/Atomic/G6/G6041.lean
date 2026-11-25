import Mathlib
import NlsGge.Atomic.G6.G6041ConeCore
import NlsGge.Atomic.G6.G6041Diag
import NlsGge.Atomic.G6.G6041DiagLeaf
import NlsGge.Atomic.G6.G6033
import NlsGge.Atomic.G6.G6036Core

                                                                                                                 
                                                                                                             
                                                                                                                
                                                                                                   
                                                                                                                
                                                                                                          
                                                                                    
                                          
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6041 (I : PositiveActionSpace) : AnalyticAtCone actionHamiltonian I :=
  NlsGge.ThirdConsultation.G6041S.cone_of NlsGge.ThirdConsultation.G6041S.diagonalHamiltonian_analytic
    (fun n x => NlsGge.ThirdConsultation.G6036S.diagH_flip G6033.2 n x)
    diagonalHamiltonian_eq_actionHamiltonian I

end
end NlsGge.GKDefinitionDesign

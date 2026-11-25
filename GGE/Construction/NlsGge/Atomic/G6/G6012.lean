import Mathlib
import NlsGge.Atomic.G6.G6011Sup1Core
import NlsGge.Atomic.G6.G6003
import NlsGge.Atomic.G6.G6009

                                                                                                            
                                                                                                                                  
                                                                                                                       
                                                                     
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6012 :
  IsOpen {z : CartesianReal | ∃! u : PhysicalL2, realBirkhoffCartesian u = z} := by
  exact G6011Aux.singletonFiber_isOpen realBirkhoffCartesian G6009.1 G6003

end
end NlsGge.GKDefinitionDesign

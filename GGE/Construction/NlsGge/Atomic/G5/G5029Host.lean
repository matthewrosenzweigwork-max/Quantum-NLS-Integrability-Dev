import Mathlib
import NlsGge.GK38.DirichletRealReality
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38

                                                                                                                
                                                                                                                                      
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- All left Dirichlet points, including collapsed gaps. -/
def AllDirichletLeft (u : PhysicalL2) : Prop :=
  ∀ n : ℤ, gkMu u n = NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n

end
end NlsGge.GKDefinitionDesign

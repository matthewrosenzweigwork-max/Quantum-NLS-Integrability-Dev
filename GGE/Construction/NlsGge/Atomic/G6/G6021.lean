import Mathlib
import NlsGge.Atomic.G6.G6021Sup1Core
import NlsGge.Atomic.G6.G6018
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6013Sup1
import NlsGge.Atomic.G6.G6014
import NlsGge.Atomic.G6.G6015
import NlsGge.Atomic.G6.G6020

                                                                                                             
                                                                                                          
                                                                                                                      
                                                                                                                          
                                                                                                       
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6021 (u : PhysicalL2) :
  Set.BijOn realBirkhoffCartesian (isospectralSet u) (actionTorus (actionSequence u)) ∧
  Set.BijOn physicalBirkhoff (isospectralSet u) (physicalActionTorus (actionSequence u)) :=
  G6021Aux.core21 G6018 G6013.1 G6013.2.2.2.2.1 G6013.2.2.2.2.2 G6014.2.2.2.1
    exists_physicalCartesianEquiv u

end
end NlsGge.GKDefinitionDesign

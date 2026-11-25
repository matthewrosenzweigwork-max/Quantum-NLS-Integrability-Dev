import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Atomic.G6.G6003Sup1Core
import NlsGge.Atomic.G6.G6002
import NlsGge.Atomic.G4.G4042

                                                                        
                                                                           
                                                                                                                                   
                                                           
                                                                                                                          
                                                                                                   
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6003 (u : PhysicalL2) :
  ∃ (U : Set PhysicalL2) (V : Set CartesianReal) (g : CartesianReal → PhysicalL2),
    IsOpen U ∧ u ∈ U ∧ IsOpen V ∧ realBirkhoffCartesian u ∈ V ∧
    AnalyticOnNhd ℝ realBirkhoffCartesian U ∧ AnalyticOnNhd ℝ g V ∧
    Set.MapsTo realBirkhoffCartesian U V ∧ Set.MapsTo g V U ∧
    (∀ v ∈ U, g (realBirkhoffCartesian v) = v) ∧
    (∀ z ∈ V, realBirkhoffCartesian (g z) = z) :=
  G6003Aux.core6003 realBirkhoffCartesian u G4042.2.2 (G6002 u).2

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import Armstrong.Frozen.RawBeta.GKRootedPiecewisePath38

                                                                                          
                                                                                             
                                                                                                               
                                                                                                                    
                                
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev SourcePotential := {φ : PotPair // φ ∈ sourceW}

def sourceGK (φ : SourcePotential) : GKPotential38 :=
  ⟨φ.1, sourceFamily.W_gk φ.2⟩

abbrev SourcePath (m : ℤ) (φ : SourcePotential) :=
  GKRootedPiecewisePath38 (sourceGK φ) m

end
end NlsGge.GKDefinitionDesign

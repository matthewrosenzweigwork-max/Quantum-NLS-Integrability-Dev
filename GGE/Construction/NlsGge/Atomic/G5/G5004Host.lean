import Mathlib
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.DirichletLabels
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

                                                                                                              
                                                                                                         
                                                                                                                   
                                                                                   
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def radiusQuotientLeading (n : ℤ) : ℂ := -((-1 : ℂ) ^ n) / 2

def radiusOmittedNormalized (n : ℤ) (φ : PotPair) : ℂ :=
  a5OmittedRootProduct38 n (φ, muSeq φ n) / (Lib.piN n : ℂ)

end
end NlsGge.GKDefinitionDesign

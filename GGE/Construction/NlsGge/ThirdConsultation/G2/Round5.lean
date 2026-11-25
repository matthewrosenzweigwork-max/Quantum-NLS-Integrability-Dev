import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.GK38.XiSqCanonical

                                                                                         
                                                                                                                                   
                                                                                     
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def actionPositiveDomain : Set NlsGge.GK38.PotPair :=
  {φ | φ ∈ sourceBetaW ∧
    ∀ n : ℤ, 0 < (NlsGge.GK38.xiSq38 n φ).re}

end
end NlsGge.GKDefinitionDesign

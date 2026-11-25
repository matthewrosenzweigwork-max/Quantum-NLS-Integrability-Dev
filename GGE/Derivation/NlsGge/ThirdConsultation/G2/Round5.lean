import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.GK38.XiSqCanonical

/- G2 ROUND5 HOST01 (proof development, AUTHOR; target NlsGge/ThirdConsultation/G2/Round5.lean).
   Hosts ONLY `actionPositiveDomain`, verbatim from Pro round 5 section 6. sourceFamily/sourceBetaW are landed in SourceFamilyBasic
   (not redeclared); realSlice is NlsGge.GK38.realSlice (imported, not redefined). -/
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

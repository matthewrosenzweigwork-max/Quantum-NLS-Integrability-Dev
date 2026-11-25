import Mathlib
import NlsGge.Atomic.G5.G5001Host
import NlsGge.GK38.TauGammaDefs

                                                                                                               
                                                                                                                     
                                                                                                            
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def cartesianLeading (n : ℤ) (a : ℤ) (φ : PotPair) : ℂ :=
  2 * (tauN φ n - muSeq φ n) +
    2 * (a : ℂ) * Complex.I * radiusQuotient n φ * antiDiscrim φ (muSeq φ n)

end
end NlsGge.GKDefinitionDesign

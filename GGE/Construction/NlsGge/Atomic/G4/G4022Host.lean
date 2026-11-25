import Mathlib
import NlsGge.Atomic.G4.G4036Host

                                                                                                               
                                                                                                                               
                                                                                                           
                                                   
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Segment integral with the removable integrand filled before integration. -/
def chi (n : ℤ) (φ : PotPair) : ℂ :=
  (muSeq φ n - tauN φ n) * ∫ t : ℝ in (0 : ℝ)..1,
    zetaDividedDifference n φ (tauN φ n + (t : ℂ) * (muSeq φ n - tauN φ n))

end
end NlsGge.GKDefinitionDesign

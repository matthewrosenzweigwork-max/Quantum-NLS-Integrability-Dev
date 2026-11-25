import Mathlib
import NlsGge.GK38.Defs
import NlsGge.GK38.IsolatingDefs
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.StdRootBranchesDefs
import NlsGge.GK38.PairRealBridge
import NlsGge.Definitions.PilotInterfaces

                                                         
                                                                                                         
                                                                                                               
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def higherAction (k : ℕ) (φ : PotPair) (n : ℤ) : ℂ :=
  (1/(Real.pi : ℂ)) * circleIntegral
    (fun z : ℂ => z^k * deriv (discrim φ) z / canonRoot38 φ z)
    (discC φ n) (discR φ n)

end
end NlsGge.GKDefinitionDesign

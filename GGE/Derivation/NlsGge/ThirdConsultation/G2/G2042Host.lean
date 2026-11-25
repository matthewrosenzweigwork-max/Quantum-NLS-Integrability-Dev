import Mathlib
import NlsGge.GK38.Defs
import NlsGge.GK38.IsolatingDefs
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.StdRootBranchesDefs
import NlsGge.GK38.PairRealBridge
import NlsGge.Definitions.PilotInterfaces

/- G2-042 HOST01 (proof development, AUTHOR; not self-reviewed).
   Hosts the design definition `higherAction` byte-identically from DEFINITIONS/G2.lean.md (lines 92-95),
   (The elaboration probe G2042HeadProbe was removed by root before landing, per review proof development note 1.) -/
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

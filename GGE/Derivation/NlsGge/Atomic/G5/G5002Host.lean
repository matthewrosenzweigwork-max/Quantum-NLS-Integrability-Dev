import Mathlib
import NlsGge.Atomic.G5.G5001Host
import NlsGge.GK38.TauGammaDefs

/- G5002 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5002Host.lean.
   Body of `cartesianLeading` verbatim from DEFINITIONS/G5.lean.md (followup12, line 63; Pro round 14 section G5-002:
   "host the current literal design bodies once"). No lexical edits. Not previously landed (grep NlsGge). -/
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

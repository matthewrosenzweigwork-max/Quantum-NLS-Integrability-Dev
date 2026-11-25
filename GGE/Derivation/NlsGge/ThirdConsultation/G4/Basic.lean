import Mathlib
import NlsGge.Atomic.G4.G4027
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.TauGammaDefs

/- Host draft for NlsGge/ThirdConsultation/G4/Basic.lean (proof development, AUTHOR). Hosts ONLY elementaryEtaIntegral, copied verbatim
   from DEFINITIONS/G4.lean.md lines 71-73 (namespace NlsGge.GKDefinitionDesign as G4017/G4024/G4027 hosts). Checked: no production
   definition of elementaryEtaIntegral; no NlsGge/ThirdConsultation/G4 directory exists. elementarySlitIntegral comes from landed G4027. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def elementaryEtaIntegral (n : ℤ) (φ : PotPair) : ℂ :=
  if lamPlus φ n = lamMinus φ n then 0
  else elementarySlitIntegral (lamPlus φ n - lamMinus φ n) (tauN φ n) (muSeq φ n)

end
end NlsGge.GKDefinitionDesign

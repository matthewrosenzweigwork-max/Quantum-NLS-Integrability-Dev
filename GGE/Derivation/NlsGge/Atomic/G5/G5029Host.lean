import Mathlib
import NlsGge.GK38.DirichletRealReality
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38

/- G5-029 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5029Host.lean.
   Hosts `AllDirichletLeft` VERBATIM from followup12 DEFINITIONS/G5.lean.md (line 85-87). Grep of NlsGge/ (2026-11-01): not landed. -/
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- All left Dirichlet points, including collapsed gaps. -/
def AllDirichletLeft (u : PhysicalL2) : Prop :=
  ∀ n : ℤ, gkMu u n = NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u n

end
end NlsGge.GKDefinitionDesign

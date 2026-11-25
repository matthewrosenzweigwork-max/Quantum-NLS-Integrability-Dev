import Mathlib
import NlsGge.Atomic.G2.G2048
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

/- G3 ZETA HOST (proof development, AUTHOR; not self-reviewed). Hosts the design name `betaZeta`, body verbatim from
   followup4 DEFINITIONS/G3.lean.md (sha256 c3e83697...). Shared host: every G3 packet that needs betaZeta
   imports NlsGge.Atomic.G3.G3ZetaHost and must not redeclare it. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def betaZeta (n m : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  psiZeta φ (p2Extend38 n (sourceF n φ)) n m z

end
end NlsGge.GKDefinitionDesign

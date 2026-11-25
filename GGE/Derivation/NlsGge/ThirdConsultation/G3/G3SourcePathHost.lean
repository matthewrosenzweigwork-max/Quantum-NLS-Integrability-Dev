import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import Armstrong.Frozen.RawBeta.GKRootedPiecewisePath38

/- G3-001 SOURCE-PATH HOST (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/ThirdConsultation/G3/G3SourcePathHost.lean (name proposed; root to confirm).
   Bodies VERBATIM from Pro round 9 DEFINITIONS/G3.lean.md first block (SourcePotential, sourceGK, SourcePath).
   Shared host: every G3 packet whose head mentions SourcePotential/sourceGK/SourcePath imports this module and must
   not redeclare these names. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev SourcePotential := {φ : PotPair // φ ∈ sourceW}

def sourceGK (φ : SourcePotential) : GKPotential38 :=
  ⟨φ.1, sourceFamily.W_gk φ.2⟩

abbrev SourcePath (m : ℤ) (φ : SourcePotential) :=
  GKRootedPiecewisePath38 (sourceGK φ) m

end
end NlsGge.GKDefinitionDesign

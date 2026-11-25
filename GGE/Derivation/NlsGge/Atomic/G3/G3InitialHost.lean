import Mathlib
import NlsGge.Atomic.G3.G3SegmentHost

/- G3 INITIAL HOST (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/G3/G3InitialHost.lean, namespace
   NlsGge.GKDefinitionDesign. Hosts the design name betaInitialSegment, body VERBATIM from followup5
   DEFINITIONS/G3.lean.md lines 57-58 (sha256 c3e83697...). betaSegmentDensity is imported from G3SegmentHost, not redeclared.
   Shared host: the G3-018 packet imports this module and must not redeclare the name. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def betaInitialSegment (n m : ℤ) (φ : PotPair) (ε : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..ε, betaSegmentDensity n m φ t

end
end NlsGge.GKDefinitionDesign

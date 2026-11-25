import Mathlib
import NlsGge.Atomic.G3.G3019
import NlsGge.ThirdConsultation.G2.G2071Support1
import NlsGge.Atomic.G2.G2019

/- G3 RATIO HOST (proof development, AUTHOR; not self-reviewed). Hosts the design name `betaRootRatioAlong`, body verbatim from
   followup4 DEFINITIONS/G3.lean.md (sha256 c3e83697...). Shared host: every G3 packet that needs it
   imports NlsGge.Atomic.G3.G3RatioHost and must not redeclare it. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def betaRootRatioAlong (n m : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  (normalizedRoot n m φ - betaSegmentPoint m φ t) /
    standardRoot φ m (betaSegmentPoint m φ t)

end
end NlsGge.GKDefinitionDesign

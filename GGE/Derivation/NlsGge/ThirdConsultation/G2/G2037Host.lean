import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G2.G2019

/- G2-037 HOST (proof development, AUTHOR; not self-reviewed). Shared design definitions for the G2-037 family,
   byte-identical from DEFINITIONS/G2.lean.md (root/gpt6pro_followup5 handoff, lines 190-195).
   Owner: G2-037 family (G2-038 and G2-044 reuse these names). No statement or hypothesis is added. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def finiteGapCuts (u : PhysicalL2) (S : Finset ℤ) : Set ℂ :=
  ⋃ n ∈ (S : Set ℤ), gapSegment (realSlice u) n

def finiteGapDifferential (u : PhysicalL2) (S : Finset ℤ) (z : ℂ) : ℂ :=
  -Complex.I * ∏ n ∈ S,
    (lamDot (realSlice u) n-z)/standardRoot (realSlice u) n z

end
end NlsGge.GKDefinitionDesign

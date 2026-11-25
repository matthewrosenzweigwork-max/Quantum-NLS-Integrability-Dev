import Mathlib
import NlsGge.GK38.DirichletRealReality
import NlsGge.GK38.GradFundamentalDefs
import NlsGge.GK38.PairRealBridge
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38

/- G1-083 HOST01 (proof development, AUTHOR; not reviewed). Hosts the Pro design definitions signedDirichletData, gapCircle,
   gapCircleProduct VERBATIM from root/gpt6pro_followup11 DEFINITIONS/G1.lean.md (lines 55-64).
   Grep check: none of the three names occurs in NlsGge/ (production) at time of writing.
   Target NlsGge/Atomic/G1/G1083Host.lean. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def signedDirichletData (u : PhysicalL2) (n : ℤ) : ℝ × ℝ :=
  (gkMu u n, (antiDiscrim (realSlice u) (gkMu u n : ℂ)).re)

def gapCircle (u : PhysicalL2) (n : ℤ) : Set (ℝ × ℝ) :=
  {p | actualGapLowerAllE02_38 u n ≤ p.1 ∧
    p.1 ≤ actualGapUpperAllE02_38 u n ∧
    p.2^2 = (discrim (realSlice u) (p.1 : ℂ)).re^2 - 4}

def gapCircleProduct (u : PhysicalL2) : Set (ℤ → ℝ × ℝ) :=
  {p | ∀ n : ℤ, p n ∈ gapCircle u n}

end
end NlsGge.GKDefinitionDesign

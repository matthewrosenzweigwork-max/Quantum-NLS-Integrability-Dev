import Mathlib
import NlsGge.GK38.PoissonSpectralModel
import NlsGge.GK38.DirichletRealReality

/- G1-081 HOST01 (proof development, AUTHOR; not reviewed). Hosts the Pro design definitions singleGapField, completeGapFlow, singleGapFlow
   VERBATIM from root/gpt6pro_followup11 DEFINITIONS/G1.lean.md (section "The actual complete one-gap flow", lines 261-275).
   Grep check: none of the three names occurs in NlsGge/ (production) at time of writing.
   Target NlsGge/Atomic/G1/G1081Host.lean. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.PoissonSpectral38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def singleGapField (n : ℤ) (u : PhysicalL2) : PhysicalL2 :=
  (spectralDiscrimHamField38 (realSlice u) (gkMu u n : ℂ)).1

def completeGapFlow (n : ℤ) (f : ℝ → PhysicalL2 → PhysicalL2) : Prop :=
  (∀ u : PhysicalL2, f 0 u = u) ∧
  (∀ u : PhysicalL2, ∀ t : ℝ,
    HasDerivAt (fun s : ℝ => f s u) (singleGapField n (f t u)) t)

open Classical in
def singleGapFlow (n : ℤ) : ℝ → PhysicalL2 → PhysicalL2 :=
  if h : ∃ f : ℝ → PhysicalL2 → PhysicalL2, completeGapFlow n f then
    Classical.choose h
  else fun _ u => u

end
end NlsGge.GKDefinitionDesign

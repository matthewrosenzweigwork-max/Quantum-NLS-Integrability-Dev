import Mathlib
import NlsGge.Atomic.G1.G1036
import NlsGge.ThirdConsultation.G1.Round6

/- G1-037 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1037Host.lean.
   Definition only; no theorem. Body of wkbSigma is byte-identical to the Pro round 9 design text
   (root/gpt6pro_followup7 DEFINITIONS/G1.lean.md lines 186-187), except the lexical repair of the spectral
   parameter name lambda -> l (lambda is a Lean keyword), as in the landed Round7 host (wkbPartial).
   `grep -rn "def wkbSigma" NlsGge` was empty at authoring time. -/
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section

def wkbSigma (N : ℕ) (l : ℂ) (φ : PotPair) : ℂ :=
  -Complex.I*l - hierarchyHamiltonian 1 φ / (2*Complex.I*l) +
    ∑ k ∈ Finset.Icc 2 N, hierarchyHamiltonian k φ / (2*Complex.I*l)^k

end
end NlsGge.GKDefinitionDesign

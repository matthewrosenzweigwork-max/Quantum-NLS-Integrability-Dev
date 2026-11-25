import Mathlib
import NlsGge.Atomic.G4.G4NormalizedHost

/- G4-048 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4048Host.lean.
   Hosts ONLY the design predicate `NormalizedZetaGapBound`, body verbatim from
   root/gpt6pro_followup9 DEFINITIONS/G4.lean.md (identical in followup2..9). `sourceBetaW` is the landed SourceFamilyBasic
   host (imported through G4NormalizedHost); `normalizedZeta` is the landed G4NormalizedHost def. Grep of NlsGge/ and
   Work/ finds no other definition of `NormalizedZetaGapBound`. Lexical repairs: none. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def NormalizedZetaGapBound (V : Set PotPair) (L : ℝ) : Prop :=
  0 ≤ L ∧ V ⊆ sourceBetaW ∧
  ∀ φ ∈ V, ∀ n : ℤ,
    ‖normalizedZeta n φ (tauN φ n) - 1‖ ≤ L * ‖lamPlus φ n - lamMinus φ n‖

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.Atomic.G4.G4036Host

/- G4022 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4022Host.lean.
   Hosts the design object `chi` (followup9 DEFINITIONS/G4.lean.md:60-63; body and docstring verbatim, no lexical edit needed).
   `zetaDividedDifference` is already landed in NlsGge/Atomic/G4/G4036Host.lean (imported, not redeclared).
   grep NlsGge (2026-10-31): no other `def chi`. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Segment integral with the removable integrand filled before integration. -/
def chi (n : ℤ) (φ : PotPair) : ℂ :=
  (muSeq φ n - tauN φ n) * ∫ t : ℝ in (0 : ℝ)..1,
    zetaDividedDifference n φ (tauN φ n + (t : ℂ) * (muSeq φ n - tauN φ n))

end
end NlsGge.GKDefinitionDesign

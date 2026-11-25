import Mathlib
import NlsGge.Atomic.G4.G4017
import NlsGge.Atomic.G4.G4022Host
import NlsGge.Atomic.G4.G4036Host

/- G4028 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4028Host.lean.
   Hosts the design object `collapsedZValue` (design DEFINITIONS/G4.lean.md, identical in followup9 and followup10;
   body verbatim, no lexical edit needed: no `lambda` binder). `chi` is landed in G4022Host, `sheetSign` in G4017,
   `tauN`/`muSeq` come from GK38; cartesianZ / cartesianZExtended are landed in G4036Host.
   grep NlsGge and Work/isolated_20261027 (2026-10-31): no other `def collapsedZValue`. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def collapsedZValue (n : ℤ) (a : ℤ) (φ : PotPair) : ℂ :=
  2 * (tauN φ n - muSeq φ n) * (1 + (a : ℂ) * sheetSign n φ) *
    Complex.exp (chi n φ)

end
end NlsGge.GKDefinitionDesign

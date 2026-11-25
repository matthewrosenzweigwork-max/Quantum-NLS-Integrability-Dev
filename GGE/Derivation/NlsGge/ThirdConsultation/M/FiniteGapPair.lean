import Mathlib
import NlsGge.Atomic.G2.G2046

/- finiteGapPair HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/ThirdConsultation/M/FiniteGapPair.lean, module NlsGge.ThirdConsultation.M.FiniteGapPair.
   Hosts ONLY `finiteGapPair`, body VERBATIM from followup13 DEFINITIONS/M.lean.md "Round14 — authoritative additions and
   replacements" (L1955-1956; identical in followup12, sha b0fe5bd6f2a3…). grep NlsGge/ (2026-11-02): not declared
   anywhere (only mentioned in comments of M016ChartCore/M016ChartFinal/M014Host). Imports the landed host of
   `NlsGge.GKDefinitionDesign.gap` (Atomic/G2/G2046). Needs ROOT MAIN PROBE (G2046 absent from the mirror). -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

def finiteGapPair (φ : PotPair) : Prop :=
  {n : ℤ | NlsGge.GKDefinitionDesign.gap φ n ≠ 0}.Finite

end NlsGge.ThirdConsultation.M

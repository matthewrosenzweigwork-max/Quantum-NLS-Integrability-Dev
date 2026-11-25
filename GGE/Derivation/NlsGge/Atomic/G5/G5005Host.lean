import Mathlib
import NlsGge.GK38.Defs
import NlsGge.GK38.PairPotential

/- G5-005 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5005Host.lean.
   Hosts the two design-only definitions used by the G5005 head: pairGradientNorm and fourierMode.
   Bodies byte-identical to the newest DEFINITIONS/G5.lean.md (root/gpt6pro_followup8/handoff/definitions_design_20261027/DEFINITIONS/G5.lean.md,
   lines 86-87 and 105-107; same text in followup5).  Names grepped absent from NlsGge/ (2026-10-31). No lexical edits. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Squared paired norm, not the house product's maximum norm. -/
def pairGradientNorm (v : PotPair) : ℝ := Real.sqrt (‖v.1‖^2 + ‖v.2‖^2)

def fourierMode (a : ℤ) (n : ℤ) : PotPair :=
  if a = 1 then (0, fourierLp (T := (1 : ℝ)) 2 (-n))
  else (fourierLp (T := (1 : ℝ)) 2 n, 0)

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.ThirdConsultation.M.M021Host
import NlsGge.ThirdConsultation.M.M031Host
import NlsGge.Atomic.M.M005
import NlsGge.Atomic.M.M054
import NlsGge.GK38.Defs

/-!
# M-033/M-034 host: the Molnar pair H1 norm and the two H1 label thresholds (proof development, AUTHOR; not self-reviewed)

Three definitions, verbatim from Pro round 14 (2d599b57), DEFINITIONS/M.lean.md (followup12) "Round14 — authoritative
additions and replacements": `MTwoMode.H1Norm`, `M.LowModeH1Threshold`, `M.HighModeH1Threshold`.  Not previously
landed (grep of NlsGge/ on 2026-11-01).  Reused owners: `MTwoMode.potentialCoefficientNorm` (M021Host),
`M.sourceH1Weight` (M031Host), `M.SobolevR`/`M.physicalOfSobolev` (M005), `realSlice` (GK38.Defs),
`M054.indexWeight` (M054).  Lexical additions only: `noncomputable section` and `open NlsGge.GK38` for `realSlice`.
-/

set_option autoImplicit false

noncomputable section

open NlsGge.GK38

namespace NlsGge.ThirdConsultation.MTwoMode

/-- Only define the H1 value on an actual H1 carrier. -/
def H1Norm (u : M.SobolevR 1) : ℝ :=
  potentialCoefficientNorm M.sourceH1Weight (realSlice (M.physicalOfSobolev u))

end NlsGge.ThirdConsultation.MTwoMode

namespace NlsGge.ThirdConsultation.M

/-- Exact source low threshold; a strict inequality, with no L2 replacement. -/
def LowModeH1Threshold (u : SobolevR 1) (n : ℤ) : Prop :=
  NlsGge.Atomic.M.M054.indexWeight n < 8 * MTwoMode.H1Norm u ^ 2

/-- The nonzero label is part of the source two-sided comparison. -/
def HighModeH1Threshold (u : SobolevR 1) (n : ℤ) : Prop :=
  n ≠ 0 ∧ 8 * MTwoMode.H1Norm u ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n

end NlsGge.ThirdConsultation.M

end

import Mathlib
import NlsGge.ThirdConsultation.R.R109Host

/- R110HOST HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORTING host (no packet increment), target
   NlsGge/ThirdConsultation/R/R110Host.lean. Hosts ONLY `actualRamerDensity`, body VERBATIM from followup13
   DEFINITIONS/R.lean.md "Round14" fixed-realization block (L963-966), the remaining name of that block consumed by
   R-110. It uses weightedK (landed R100Host) and canonicalDelta (proof development's R109Host, the shared semantic unit with
   canonicalDelta_spec, r14 l.5930) — so this host must follow R109Host. grep NlsGge/ (2026-11-03): not declared.
   Needs ROOT MAIN PROBE. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer

namespace NlsGge.ThirdConsultation.R
noncomputable section

def actualRamerDensity {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) : ECarrier38 c s → ℝ :=
  NlsGge.Birkhoff.fW06_38 c s hs (weightedK c s hs1)
    (canonicalDelta c s hs hs1)

end
end NlsGge.ThirdConsultation.R

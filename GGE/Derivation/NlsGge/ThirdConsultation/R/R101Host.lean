import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52

/- R101HOST HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORTING host (no packet increment), target
   NlsGge/ThirdConsultation/R/R101Host.lean. Hosts ONLY `actualWeightedBirkhoffHomeo`, docstring and body VERBATIM from
   followup13 DEFINITIONS/R.lean.md "Round14" fixed-realization block (L918-922; block preamble L911-918 kept). It is
   the actual weightedHomeoE38 at the landed realized pair. grep NlsGge/ (2026-11-03): not declared. Consumer: R-101.
   (weightedK/Kinv of the same block are in R100Host.) Needs ROOT MAIN PROBE. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- The actual E_s homeomorphism, without any artificial s-window on this deterministic map. -/
def actualWeightedBirkhoffHomeo {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ) :
    ECarrier38 c s ≃ₜ ECarrier38 c s :=
  PDE.actualBirkhoffInput38.weightedHomeoE38 PDE.actualOneSmoothingInput38 c s

end
end NlsGge.ThirdConsultation.R

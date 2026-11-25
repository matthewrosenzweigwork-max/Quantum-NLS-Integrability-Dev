import Mathlib
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52

/- R111HOST HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORTING host (no packet increment), target
   NlsGge/ThirdConsultation/R/R111Host.lean. Hosts ONLY `actualFourierGaussian`, docstring and body VERBATIM from
   followup13 DEFINITIONS/R.lean.md "Round14" fixed-realization block (L968-971): the literal Gaussian pushforward
   (fullWeightedSequenceGaussian c s).map (physFW06_38 c s). grep NlsGge/ (2026-11-03): not declared. Consumer: R-111.
   Needs ROOT MAIN PROBE. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- Same literal Gaussian pushforward as gammaF_eq_W06_38. -/
def actualFourierGaussian {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) : Measure PhysicalL2 :=
  (fullWeightedSequenceGaussian c s).map (physFW06_38 c s)

end
end NlsGge.ThirdConsultation.R

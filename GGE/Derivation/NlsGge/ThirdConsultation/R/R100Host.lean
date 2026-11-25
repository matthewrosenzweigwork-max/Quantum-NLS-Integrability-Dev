import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52

/- R100HOST HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORTING host (no packet increment), target
   NlsGge/ThirdConsultation/R/R100Host.lean. Hosts ONLY `weightedK` and `Kinv`, bodies VERBATIM from followup13
   DEFINITIONS/R.lean.md "Round14" fixed-realization block (L926-934; preamble L911-918 kept), consumed by R-100's
   printed `actual_CM_difference_analytic`. grep NlsGge/ (2026-11-03): neither name (nor any other name of that block)
   is declared. They are thin names for the landed W06 maps KW06_38 / KinvW06_38 at the actual realized pair. The other
   definitions of that block belong to their own consumers and are NOT hosted here. Needs ROOT MAIN PROBE. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer

namespace NlsGge.ThirdConsultation.R
noncomputable section

def weightedK {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (hs1 : s ≤ 1) : ECarrier38 c s → ActualCM c :=
  PDE.actualBirkhoffInput38.KW06_38 PDE.actualOneSmoothingInput38 c hs1

def Kinv {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (hs1 : s ≤ 1) : ECarrier38 c s → ActualCM c :=
  PDE.actualBirkhoffInput38.KinvW06_38 PDE.actualOneSmoothingInput38 c hs1

end
end NlsGge.ThirdConsultation.R

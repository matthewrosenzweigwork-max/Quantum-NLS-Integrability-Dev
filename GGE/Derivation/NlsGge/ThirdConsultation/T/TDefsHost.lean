import Mathlib
import NlsGge.ThirdConsultation.I.LimitLaws
import NlsGge.Weights.Entire
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.ThirdConsultation.R.R109Host
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.ThirdConsultation.T.ECarrier98
import NlsGge.Hierarchy.ExponentialH2Moment38
import NlsGge.Measure.CountableReconstruction

/- TDEFSHOST HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORTING host (no packet increment),
   target NlsGge/ThirdConsultation/T/TDefsHost.lean (named TDefsHost, not T008Host: followup13 STATEMENTS/T.md prints
   `ZW c` in T-008/T-009/T-014/T-033, `muWE` in T-008/T-010/T-011, `fullFourierDensity` in T-014). Hosts ONLY
   `ZW`, `fullFourierDensity`, `muWE`, bodies VERBATIM from followup13 DEFINITIONS/T.lean.md (L255, L266, L280), under
   that printed block's preamble (L242-250) verbatim. No reduction applied. `ECarrier38 c s` is the plain def
   `FullWeightedHilbert c s` (W04WeightedSmoothing38:41), so the withDensity of `fullWeightedSequenceGaussian c s`
   is a `Measure (ECarrier38 c s)` definitionally; its MeasurableSpace instance is the landed ECarrier98 one
   (inferInstanceAs). grep NlsGge/ (2026-11-03): none of the three names declared. Needs ROOT MAIN PROBE. -/
set_option autoImplicit false
open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Birkhoff
open NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.T
noncomputable section

def ZW {lo up : ℝ} (c : BoundedCoefficients lo up) : ℝ :=
  I.limitNormalizer (weight c.val)

def fullFourierDensity {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ECarrier38 c s → ℝ :=
  fW06_38 c s hs
    (PDE.actualBirkhoffInput38.KW06_38 PDE.actualOneSmoothingInput38 c
      (le_one_of_lt_three_quarters_W06_38 hs'))
    (R.canonicalDelta c s hs (le_one_of_lt_three_quarters_W06_38 hs'))

def muWE {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    Measure (ECarrier38 c s) :=
  ENNReal.ofReal (ZW c)⁻¹ •
    (fullWeightedSequenceGaussian c s).withDensity
      (fun x => ENNReal.ofReal (fullFourierDensity c s hs hs' x))

end
end NlsGge.ThirdConsultation.T

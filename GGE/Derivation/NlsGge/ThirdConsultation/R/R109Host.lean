import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.ThirdConsultation.R.R100Host

/- R109HOST HOST02 (CANDIDATE) (proof development, AUTHOR; not reviewed). SHARED host (r14 l.5930: "The R.canonicalDelta body is owned by the
   R109 shared host"), target NlsGge/ThirdConsultation/R/R109Host.lean, namespace NlsGge.ThirdConsultation.R. Hosts
   canonicalDelta, canonicalDelta_spec (its required prior semantic-unit projection, printed WITH its proof) and
   actualRamerJac, bodies VERBATIM from r14 PRO_DEFINITION_RESPONSE_FP80_14.md l.3722-3744 (= followup13 DEFINITIONS/R.lean.md
   round-14 fixed-realization block, string-checked). grep NlsGge/ and Work/ (2026-11-03): none of the three declared.
   weightedK is reused from landed R100Host. The choice is from the landed, proved W06Jacobian38.ramer_W06_38 at the
   actual pair (before W07/W11); no provisional definition.
   LEXICAL REPAIR CANDIDATE (needs root/owner approval): Pro's two calls `PDE.actualBirkhoffInput38.ramer_W06_38
   PDE.actualOneSmoothingInput38 c s hs hs1` do not elaborate: ramer_W06_38 is NlsGge.Birkhoff.ramer_W06_38 (section Main of
   W06Jacobian38, B explicit), not NlsGge.Birkhoff.BirkhoffInput38.ramer_W06_38, so the dot projection fails (replica lane
   eee0c419 "Invalid field ramer_W06_38"). Repair: the non-dotted application `NlsGge.Birkhoff.ramer_W06_38
   PDE.actualBirkhoffInput38 PDE.actualOneSmoothingInput38 c s hs hs1` (same constant, same arguments, the term the dot
   form denotes; as landed W10Localized38f:109 calls it). No other change. Needs ROOT MAIN PROBE (OneSmoothing). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- Choice from the already proved Ramer theorem, before W07/W11 is used. -/
noncomputable def canonicalDelta {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) : (ℤ → ℂ) → ℝ :=
  Classical.choose (NlsGge.Birkhoff.ramer_W06_38 PDE.actualBirkhoffInput38
    PDE.actualOneSmoothingInput38 c s hs hs1)

theorem canonicalDelta_spec {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) :
    NlsGge.Birkhoff.RamerDivergence38 c s
      (PDE.actualBirkhoffInput38.KW06_38 PDE.actualOneSmoothingInput38 c hs1)
      (canonicalDelta c s hs hs1)
 :=
  (Classical.choose_spec (NlsGge.Birkhoff.ramer_W06_38 PDE.actualBirkhoffInput38
    PDE.actualOneSmoothingInput38 c s hs hs1)).1


def actualRamerJac {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) : ECarrier38 c s → ℝ :=
  NlsGge.Birkhoff.JW06_38 c s hs (weightedK c s hs1)
    (canonicalDelta c s hs hs1)

end
end NlsGge.ThirdConsultation.R

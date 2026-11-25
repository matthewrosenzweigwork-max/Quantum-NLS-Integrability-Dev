import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.ThirdConsultation.R.R100Host
import NlsGge.ThirdConsultation.R.R101Host
import NlsGge.ThirdConsultation.R.R109Host
import NlsGge.ThirdConsultation.T.ECarrier98

/- R-109 PRODUCTION01 (proof development, AUTHOR; not reviewed). PACKET R-109, target NlsGge/Atomic/R/R109.lean (TASK_INDEX,
   REUSE/EXTRACT). Preamble and head `canonicalDelta_characterization` VERBATIM from followup13 STATEMENTS/R.md §R-109
   (= r14, string-checked; r16 no change). The packet's second printed theorem `canonicalDelta_spec` is hosted in
   R109Host as Pro directs ("must be hosted with canonicalDelta as one semantic unit"); its type there is string-identical
   to the packet head. No `B.` in either head, so repair 24 is not needed. Proof (with the same lexical repair candidate as R109HOST HOST02 on the ramer_W06_38 call): Classical.choose_spec of the landed
   W06Jacobian38.ramer_W06_38 at the actual pair (exact source reuse printed by Pro); weightedK = KW06_38,
   actualWeightedBirkhoffHomeo = weightedHomeoE38 = TW06_38, actualRamerJac = JW06_38(weightedK, canonicalDelta),
   ECarrier38 = FullWeightedHilbert, all by their landed / hosted definitions.
   Own imports (B1 lesson): T.ECarrier98 (MeasurableSpace/BorelSpace on ECarrier38 for the head's `fun x : ECarrier38 c s`,
   = FullWeightedHilbert instance by inferInstanceAs), OneSmoothing (notations, actual pair), W06Jacobian38, R100Host (weightedK), R101Host (h809,
   actualWeightedBirkhoffHomeo; in probe q267), R109Host; the rest provide the preamble namespaces. MAIN-ONLY. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem canonicalDelta_characterization {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs1 : s ≤ 1) :
    RamerDivergence38 c s (weightedK c s hs1) (canonicalDelta c s hs hs1) ∧
    (fullWeightedSequenceGaussian c s).map (actualWeightedBirkhoffHomeo c s).symm =
      (fullWeightedSequenceGaussian c s).withDensity
        (fun x : ECarrier38 c s => ENNReal.ofReal (actualRamerJac c s hs hs1 x)) ∧
    (∀ x : ECarrier38 c s, 0 < actualRamerJac c s hs hs1 x) ∧
    Integrable (actualRamerJac c s hs hs1) (fullWeightedSequenceGaussian c s) ∧
    (∫ x : ECarrier38 c s, actualRamerJac c s hs hs1 x
      ∂(fullWeightedSequenceGaussian c s)) = 1 :=
  Classical.choose_spec (NlsGge.Birkhoff.ramer_W06_38 PDE.actualBirkhoffInput38
    PDE.actualOneSmoothingInput38 c s hs hs1)

end NlsGge.ThirdConsultation.R

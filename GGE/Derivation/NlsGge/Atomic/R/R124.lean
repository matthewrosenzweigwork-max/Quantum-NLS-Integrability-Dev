import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

/- R-124 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). PACKET R-124, target
   NlsGge/Atomic/R/R124.lean (TASK_INDEX, REUSE/EXTRACT). Head and preamble VERBATIM from followup13 STATEMENTS/R.md
   §R-124 (= r14 PRO_DEFINITION_RESPONSE_FP80_14.md L4633-4650; r16 no change), with OWNER-APPROVED lexical repair 24
   (AUDIT_DEFERRED_NOTES01 L363): the printed `B.KE38` (B a local notation) is written `(B).KE38` (two occurrences);
   tokens, order and meaning unchanged.
   Proof: the printed exact landed source reuse `Birkhoff/W09Approx38b.lean:tendsto_tail_DKE38` at the actual pair
   B = PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38 (both landed). The extra imports only provide the
   namespaces opened by the printed preamble (as in landed R-118). Needs ROOT MAIN PROBE.
   Q2 check: no uniform constant or selection is introduced; the statement is pointwise in x and the reuse proves exactly
   it (operator-norm tail via the E_(s-1) → E_s inclusion tail factor). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r124_main {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (x : ECarrier38 c s) :
    Tendsto (fun N : ℕ => ‖fderiv ℝ ((B).KE38 O c s) x -
      (projE38 c s N).comp (fderiv ℝ ((B).KE38 O c s) x)‖) atTop (𝓝 0) :=
  (B).tendsto_tail_DKE38 O c s x

end NlsGge.ThirdConsultation.R

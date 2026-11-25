import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

/- R-099 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). PACKET R-099, target
   NlsGge/Atomic/R/R099.lean (TASK_INDEX, REUSE/EXTRACT; prerequisites landed). Head and preamble VERBATIM from
   followup13 STATEMENTS/R.md §R-099 (= r14; r16 no change) except the owner-APPROVED lexical repair 24
   (`B.field` → `(B).field` under the `local notation "B"`; AUDIT_DEFERRED_NOTES01). Proof: the printed exact landed
   source reuse `W04WeightedSmoothing38c.lean:analytic_weightedHomeoE38_symm` at B = PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38. Extra imports only provide
   the namespaces opened by the printed preamble (as in landed R-098/R-118). Needs ROOT MAIN PROBE. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r099_main {lower upper : ℝ}  
    (c : BoundedCoefficients lower upper) (s : ℝ) :
    AnalyticOnNhd ℝ ((B).weightedHomeoE38 O c s).symm Set.univ :=
  BirkhoffInput38.analytic_weightedHomeoE38_symm B O c s

end NlsGge.ThirdConsultation.R

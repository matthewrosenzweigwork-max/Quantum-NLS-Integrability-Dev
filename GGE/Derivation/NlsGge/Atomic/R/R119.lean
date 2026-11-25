import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

/- R-119 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). PACKET R-119, target
   NlsGge/Atomic/R/R119.lean (TASK_INDEX, REUSE/EXTRACT; prerequisites landed). Head and preamble VERBATIM from
   followup13 STATEMENTS/R.md §R-119 (= r14; r16 no change) except the owner-APPROVED lexical repair 24
   (`B.field` → `(B).field` under the `local notation "B"`; AUDIT_DEFERRED_NOTES01). Proof: the printed exact landed
   source reuse `W08Compact38.lean:inverse_lipschitz_ballH1` at B = PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38. Extra imports only provide
   the namespaces opened by the printed preamble (as in landed R-098/R-118). Needs ROOT MAIN PROBE. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r119_main (R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ ballH1 R, ∀ y ∈ ballH1 R,
      ‖x - y‖ ≤ L * ‖(B).TC 1 x - (B).TC 1 y‖ :=
  (B).inverse_lipschitz_ballH1 O R

end NlsGge.ThirdConsultation.R

import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Birkhoff.W04WeightedSmoothing38c
import NlsGge.Birkhoff.W08Compact38
import NlsGge.Measure.WeightedScalarResidual
import NlsGge.Ramer.RamerLemma52
import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport

/- R-118 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). PACKET R-118, target
   NlsGge/Atomic/R/R118.lean (TASK_INDEX, REUSE/EXTRACT). Head and preamble VERBATIM from followup13 STATEMENTS/R.md
   §R-118 (= r14; r16 no change). Proof: the printed exact landed source reuse `W08Compact38.lean:lipschitz_Kfwd1_ballH1` at the actual pair
   B = PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38 (landed support OneSmoothing). The extra imports only
   provide the namespaces opened by the printed preamble. Needs ROOT MAIN PROBE.
   REPAIR CANDIDATE (needs root/owner approval, lexical only): the printed head writes `B.T`, `B.K_mem_E38`, `B.Kfwd1`
   with `B` a `local notation`; Lean 4 tokenizes `B.T` as the identifier `«B».T` ("Unknown identifier", worker mock
   NotationMock_RUN01 3273dd11). The ONLY change is parenthesizing the notation: `(B).T`, `(B).K_mem_E38`, `(B).Kfwd1`
   (mock NotationMock2_RUN01 6543543f exit 0). Tokens, order and meaning unchanged. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem r118_main (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ballH1 R, ∀ y ∈ ballH1 R,
      ‖(B).Kfwd1 O x - (B).Kfwd1 O y‖ ≤ C * ‖x - y‖ :=
  (B).lipschitz_Kfwd1_ballH1 O R

end NlsGge.ThirdConsultation.R

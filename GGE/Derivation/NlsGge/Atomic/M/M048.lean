import Mathlib
import NlsGge.Atomic.M.M048Core
import NlsGge.ThirdConsultation.M.OddTraceSobolev
import NlsGge.Atomic.M.M044
import NlsGge.Atomic.M.M042

/- M-048 PRODUCTION02 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe).
   Target NlsGge/Atomic/M/M048.lean, namespace NlsGge.ThirdConsultation.M.  Head `molnar_inverse_actions` verbatim from
   PRO_DEFINITION_RESPONSE_FP80_14.md L2498-2516 (with its printed open lines).
   Route: M048C.inverse_core (landed M-045/M-046/M-047 inside) with odd_higher_action_trace_sobolev (landed),
   odd_trace_action_bound (M-044) and inverse_H1_action_seed (M-042, m = 1). -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.M

theorem molnar_inverse_actions (m : ℕ) (hm : 1 ≤ m) :
  ∃ d : ℝ, 0 < d ∧ ∀ u : SobolevR m,
    ‖u‖^2 ≤
      d^2 * (actionWeightedSum m (physicalOfSobolev u) +
        (1+actionWeightedSum 1 (physicalOfSobolev u))^(4*m-3) *
          actionWeightedSum 0 (physicalOfSobolev u)) :=
  NlsGge.ThirdConsultation.M048C.inverse_core odd_higher_action_trace_sobolev
    odd_trace_action_bound inverse_H1_action_seed m hm

end NlsGge.ThirdConsultation.M

import Mathlib
import NlsGge.Atomic.M.M044Core
import NlsGge.Atomic.M.M033
import NlsGge.ThirdConsultation.M.OddActionSummable
import NlsGge.ThirdConsultation.M.OddTraceSobolev
import NlsGge.ThirdConsultation.M.CentralGap
import NlsGge.Atomic.M.M042Seed
import NlsGge.Atomic.M.M041

/- M-044 PRODUCTION02 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe).
   Target NlsGge/Atomic/M/M044.lean, namespace NlsGge.ThirdConsultation.M.  Head `odd_trace_action_bound` verbatim from
   PRO_DEFINITION_RESPONSE_FP80_14.md L2380-2399 (r14), with the r16 route (FP80_16 L534-580).
   Route: M044C.odd_trace_core with the landed M-033 comparison, MOddSum cast, odd_higher_action_trace_sobolev,
   zero_gap_small_H1, central_gap_radius, landed M042Seed.inverse_H1_source_action_seed and landed
   M041.energy_action_lower_bound. -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.M

theorem odd_trace_action_bound
    (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m) :
    actionWeightedSumENNReal m (physicalOfSobolev u) ≠ ⊤ ∧
    oddTraceEnergy m (physicalOfSobolev u) ≠ ⊤ ∧
    oddTraceSum m (physicalOfSobolev u) ≤
      actionWeightedSum m (physicalOfSobolev u) +
        (64 * Real.pi) ^ (2 * m) *
          (1 + actionWeightedSum 0 (physicalOfSobolev u)) ^ (2 * m - 1) *
          actionWeightedSum 1 (physicalOfSobolev u) ^ (2 * m - 1) :=
  NlsGge.ThirdConsultation.M044C.odd_trace_core high_odd_action_comparison
    NlsGge.ThirdConsultation.MOddSum.physicalOfSobolev_lowerSobolevCast
    odd_higher_action_trace_sobolev zero_gap_small_H1 central_gap_radius
    inverse_H1_source_action_seed energy_action_lower_bound m hm u

end NlsGge.ThirdConsultation.M

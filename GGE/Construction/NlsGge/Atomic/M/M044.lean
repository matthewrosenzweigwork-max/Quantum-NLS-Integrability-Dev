import Mathlib
import NlsGge.Atomic.M.M044Core
import NlsGge.Atomic.M.M033
import NlsGge.ThirdConsultation.M.OddActionSummable
import NlsGge.ThirdConsultation.M.OddTraceSobolev
import NlsGge.ThirdConsultation.M.CentralGap
import NlsGge.Atomic.M.M042Seed
import NlsGge.Atomic.M.M041

                                                                                                     
                                                                                                                       
                                                                                              
                                                                                                               
                                                                                                  
                                     
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

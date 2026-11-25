import Mathlib
import NlsGge.Atomic.AL.AL080
import NlsGge.Hierarchy.ALFreeFields38

                                                                               
                                                                                                    
                                                                                                             
                                                                             
set_option autoImplicit false

open NlsGge.Pilot NlsGge.AblowitzLadik NlsGge.Weights Filter Topology

namespace NlsGge.ThirdConsultation.AL

theorem al084 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    0 < 4 * Real.sqrt (2 * Real.pi) - 8 ∧
    Tendsto (fun N : ℕ => Real.log (alEdgeRatio38 c.val N) / Real.sqrt (N : ℝ))
      atTop (𝓝 (4 * Real.sqrt (2 * Real.pi) - 8)) := by
  refine ⟨?_, alEdge_log_asymptotic38 (al080Aux.admissible c)⟩
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
  have hnn := Real.sqrt_nonneg (2 * Real.pi)
  nlinarith [Real.pi_gt_three]

end NlsGge.ThirdConsultation.AL

import NlsGge.Atomic.M.M005
import NlsGge.Atomic.M.M038

                                                                                                              
                                                                                                             
                                                                                                              
                                                                                                              
                      
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.Atomic.Common
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.M

theorem top_derivative_from_charge
    (m : ℕ) (hm : 1 ≤ m) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevR m,
    topDerivativeNorm m u^2 ≤
      2*signedCharge m u +
      C*(1+‖physicalOfSobolev u‖^(4*m))*
        ‖physicalOfSobolev u‖^2 := by
  obtain ⟨C, hC0, hC⟩ := charge_remainder_absorption m hm (1 / 2 : ℝ) (by norm_num)
  refine ⟨2 * C, by linarith, fun u => ?_⟩
  have hR : chargeRemainder m u = signedCharge m u - topDerivativeNorm m u ^ 2 := rfl
  have h := abs_le.mp (hC u)
  linarith [h.1, h.2, hR]

end NlsGge.ThirdConsultation.M

import Mathlib
import NlsGge.Atomic.KSPS.KSPS003
import NlsGge.ThirdConsultation.KSPS.KSPS004Support2

                                                                                                     
                                                                                           
                                                                                                 
                                                                                             
                                                                                                      
                                                                                               
                                                                                                           
set_option autoImplicit false

open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem third_volterra_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (φ : SobolevC 1) (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
        ∀ lam : ℂ, lam ≠ 0 →
          ‖volterraTerm 3 x lam φ‖ ≤
            C * Real.exp (|lam.im| * x) *
              sobolevNorm 1 φ ^ 3 / ‖lam‖ ^ 2 := by
  obtain ⟨C3, hC3pos, hC3⟩ := second_volterra_remainder_bound
  refine ⟨((2 * ‖NlsGge.GKDefinitionDesign.iotaCLM‖ ^ 3 +
      ‖NlsGge.GKDefinitionDesign.derivCLM‖ * ‖NlsGge.GKDefinitionDesign.iotaCLM‖ ^ 2) / 4 +
      ‖NlsGge.GKDefinitionDesign.iotaCLM‖ * C3) + 1, by positivity, fun φ x hx lam hlam => ?_⟩
  exact NlsGge.ThirdConsultation.KSPS004Support2.third_core φ hx hlam hC3pos.le
    (fun t ht => hC3 φ t ht lam hlam)

end
end NlsGge.ThirdConsultation.KSPS

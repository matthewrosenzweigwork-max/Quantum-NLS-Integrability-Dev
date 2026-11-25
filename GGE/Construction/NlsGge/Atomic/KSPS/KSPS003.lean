import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPS.KSPS003Support2

                                                                                                     
                                                                                                         
                                                                                                                     
                                                                                          
set_option autoImplicit false

open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem second_volterra_remainder_bound :
  ∃ C : ℝ, 0 < C ∧ ∀ (φ : SobolevC 1)
    (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
    ∀ lam : ℂ, lam ≠ 0 →
      ‖secondVolterraRemainder φ x lam‖ ≤
        C * Real.exp (|lam.im| * x) * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2 := by
  refine ⟨(‖NlsGge.GKDefinitionDesign.iotaCLM‖ + ‖NlsGge.GKDefinitionDesign.derivCLM‖) ^ 2 + 1,
    by positivity, fun φ x hx lam hlam => ?_⟩
  exact NlsGge.ThirdConsultation.KSPS003Support2.remainder_matrix_bound φ hx hlam

end
end NlsGge.ThirdConsultation.KSPS

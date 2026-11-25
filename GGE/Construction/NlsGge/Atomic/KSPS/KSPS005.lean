import Mathlib
import NlsGge.Atomic.KSPS.KSPS003
import NlsGge.Atomic.KSPS.KSPS004
import NlsGge.ThirdConsultation.KSPS.KSPS005Host
import NlsGge.ThirdConsultation.KSPS.KSPS005Support

                                                                                                     
                                                                                                            
                                                                                                                           
                                                                                                                   
                                                                                                                       
                                                                                                                                        
                                                                                                                     
                                                                                                                                   
set_option autoImplicit false

open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem fundamental_two_term_remainder_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (φ : SobolevC 1) (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
        ∀ lam : ℂ, lam ≠ 0 →
          ‖fundamentalRemainder φ x lam‖ ≤
            C * Real.exp (|lam.im| * x + l2Norm φ) *
              sobolevNorm 1 φ ^ 2 * (1 + sobolevNorm 1 φ) / ‖lam‖ ^ 2 := by
  obtain ⟨C3, hC3, h3⟩ := second_volterra_remainder_bound
  obtain ⟨C4, hC4, h4⟩ := third_volterra_bound
  refine ⟨C3 + 2 * C4, by positivity, fun φ x hx lam hlam => ?_⟩
  exact NlsGge.ThirdConsultation.KSPS005Support.assembled_bound φ hC3 hC4
    (fun y hy mu hmu => h3 φ y hy mu hmu) (fun y hy mu hmu => h4 φ y hy mu hmu) hx hlam

theorem fundamental_two_term_remainder (φ : SobolevC 1) :
  ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ lam : ℂ, lam ≠ 0 →
    ‖fundamentalRemainder φ x lam‖ ≤
      C * Real.exp (|lam.im| * x + l2Norm φ) *
        sobolevNorm 1 φ^2 * (1+sobolevNorm 1 φ) / ‖lam‖^2 := by
  obtain ⟨C, hC, h⟩ := fundamental_two_term_remainder_uniform
  exact ⟨C, hC, fun x hx lam hlam => h φ x hx lam hlam⟩

end
end NlsGge.ThirdConsultation.KSPS

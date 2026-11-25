import Mathlib
import NlsGge.Atomic.KSPS.KSPS006
import NlsGge.ThirdConsultation.KSPS.KSPS007Host
import NlsGge.ThirdConsultation.KSPS.KSPS007Support5
import NlsGge.ThirdConsultation.KSPS.KSPS007Support9
import NlsGge.ThirdConsultation.KSPS.KSPS007Support10

                                                                                                     
                                                                                                                       
                                                                                                                   
                                                                                                 
                                                                                                          
                                                                                                                        
                                                                                                            
                                                                                                                    
                                                                                                                              
set_option autoImplicit false

open NlsGge.Pilot NlsGge.GK38
open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem forced_solution_expansion
    (LambdaIm B : ℝ) (hLambdaIm : 0 ≤ LambdaIm) (hB : 0 ≤ B) :
  ∃ C L : ℝ, 0 ≤ C ∧ 0 < L ∧
    ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
    ∀ f : PotPair, ∀ lam : ℂ, L ≤ ‖lam‖ → |lam.im| ≤ LambdaIm →
      ∀ F : ℝ → (Fin 2 → ℂ),
      NlsGge.ThirdConsultation.KSPSVolterra.ForcedZS φ lam f F →
      ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
        ‖F x -
          NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ lam f x -
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ lam f x‖ ≤
          C * NlsGge.ThirdConsultation.KSPSVolterra.vectorL2Norm f / ‖lam‖ ^ 2 := by
  obtain ⟨C6, hC6, h6⟩ := fundamental_and_inverse_two_term_remainder
  obtain ⟨K, hK0, hK⟩ := NlsGge.ThirdConsultation.KSPS007Support10.theta_pointwise LambdaIm B
    hLambdaIm hB C6 hC6.le (fun φ x hx lam hlam => h6 φ x hx lam hlam)
  refine ⟨2 * K, 1, by positivity, one_pos, ?_⟩
  intro φ hs f lam hL hΛ F hF x hx
  rw [NlsGge.ThirdConsultation.KSPS007Support9.remainder_eq_Ig φ lam f F hF hx]
  have h := NlsGge.ThirdConsultation.KSPS007Support5.Ig_norm_le f hx (b := K / ‖lam‖ ^ 2)
    (fun t ht => hK φ hs lam hL hΛ x hx t ht)
  calc _ ≤ 2 * (K / ‖lam‖ ^ 2) * Real.sqrt (‖f.1‖ ^ 2 + ‖f.2‖ ^ 2) := h
    _ = 2 * K * NlsGge.ThirdConsultation.KSPSVolterra.vectorL2Norm f / ‖lam‖ ^ 2 := by
      unfold NlsGge.ThirdConsultation.KSPSVolterra.vectorL2Norm
      ring

end
end NlsGge.ThirdConsultation.KSPS

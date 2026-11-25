import Mathlib
import NlsGge.Atomic.G6.G6040Sup1Core

                                                                                                                          
                                                                                                                  
                                                                                           
                                                                                                                
                                                                                        
set_option autoImplicit false

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem exists_local_complexification
    {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (c : (H × H) ≃L[ℝ] E)
    (hc : ∀ x y : H, c (x, y) = c (x, 0) + Complex.I • c (y, 0))
    (F : H → ℝ) (a : H) (hF : AnalyticAt ℝ F a) :
  ∃ (r : ℝ) (G : E → ℂ), 0 < r ∧
    AnalyticOnNhd ℂ G (Metric.ball (c (a, 0)) r) ∧
    ∀ x : H, c (x, 0) ∈ Metric.ball (c (a, 0)) r →
      G (c (x, 0)) = (F x : ℂ) :=
  NlsGge.ThirdConsultation.G6040S.complexification_of c hc F a hF

end
end NlsGge.GKDefinitionDesign

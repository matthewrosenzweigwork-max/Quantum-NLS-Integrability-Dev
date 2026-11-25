import Mathlib
import NlsGge.Atomic.G6.G6039Sup3Core

                                                                                                                          
                                                                                                                    
                                                                                                                  
                                                                                                 
                                                                                                      
set_option autoImplicit false

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem parametric_even_tail_descent
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    (U : Set P) (hU : IsOpen U)
    (f : P × ComplexDiagonalSpace → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (U ×ˢ Metric.ball (0 : ComplexDiagonalSpace) r))
    (heven : ∀ p : P, p ∈ U →
      CoordinatewiseEvenOn (fun x : ComplexDiagonalSpace => f (p, x))
        Set.univ (Metric.ball (0 : ComplexDiagonalSpace) r))
    (hbd : ∃ M : ℝ, ∀ (p : P) (x : ComplexDiagonalSpace),
      p ∈ U → x ∈ Metric.ball (0 : ComplexDiagonalSpace) r → ‖f (p, x)‖ ≤ M) :
  AnalyticOnNhd ℂ (parametricActionDescent f)
    (U ×ˢ Metric.ball (0 : ComplexActionSpace) (r^2)) ∧
  ∀ (p : P) (I : ComplexActionSpace) (x : ComplexDiagonalSpace),
    p ∈ U → I ∈ Metric.ball (0 : ComplexActionSpace) (r^2) →
    (∀ n : ℤ, (x n)^2 = I n) → f (p, x) = parametricActionDescent f (p, I) :=
  ⟨NlsGge.ThirdConsultation.G6039S.descent_analytic U hU f r hr hf heven hbd,
    NlsGge.ThirdConsultation.G6039S.parametric_identity U f r hr hf heven⟩

end
end NlsGge.GKDefinitionDesign

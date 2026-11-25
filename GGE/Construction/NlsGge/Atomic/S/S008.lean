import Mathlib
import NlsGge.Analysis.ConvolutionBounds

                                                                                                                                                                                                                                                                      

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis
open scoped BigOperators

namespace NlsGge.ThirdConsultation.S

theorem inverseSquareConvolution_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℤ,
      Summable
        (fun r : ℤ => inverseSquare r * inverseSquare (t - r)) ∧
      HasSum
        (fun r : ℤ => inverseSquare r * inverseSquare (t - r))
        (inverseSquareConvolution t) ∧
      (∑' r : ℤ, inverseSquare r * inverseSquare (t - r)) ≤
        C / (1 + (t : ℝ) ^ 2) :=
  ⟨uniformConvolutionConstant, uniformConvolutionConstant_pos, fun t =>
    ⟨summable_convolutionTerm t, (summable_convolutionTerm t).hasSum,
      inverseSquareConvolution_bound t⟩⟩

end NlsGge.ThirdConsultation.S
end

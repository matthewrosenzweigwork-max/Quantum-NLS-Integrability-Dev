import NlsGge.Weights.PoissonBounds

                                                                                                                  
                                                                                                              

set_option autoImplicit false
open NlsGge.Weights

namespace NlsGge.ThirdConsultation.R
noncomputable section

theorem poisson_uniform_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ t : ℝ, t ≥ 4 → ∀ j : ℕ,
      poissonTerm t j ≤ C * t ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := NlsGge.Weights.poisson_uniform_upper
  exact ⟨C, hC, fun t ht j => h t (by linarith) j⟩

end
end NlsGge.ThirdConsultation.R


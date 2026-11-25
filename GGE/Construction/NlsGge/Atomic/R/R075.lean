                                                                                                                    
                                                                                                                                                  
import NlsGge.Weights.PoissonBounds

                                                                                                                         
                                                                
                                                                              

set_option autoImplicit false
open NlsGge.Weights
open Real

namespace NlsGge.ThirdConsultation.R
noncomputable section

theorem poisson_uniform_central_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ t : ℝ, t ≥ 4 → ∀ j : ℕ,
      |(j : ℝ) - t| ≤ sqrt t → c * t ^ (-1 / 2 : ℝ) ≤ poissonTerm t j :=
  NlsGge.Weights.poisson_uniform_central_lower

end
end NlsGge.ThirdConsultation.R

import Mathlib
import NlsGge.Atomic.G6.G6041DiagCore
import NlsGge.Atomic.G6.G6031
import NlsGge.Atomic.G6.G6027

                                                                                                                          
                                                                                                       
                                                                                           
                                                                                                          
set_option autoImplicit false

open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6041S
noncomputable section

theorem diagonalHamiltonian_analytic : AnalyticOnNhd ℝ diagonalHamiltonian Set.univ :=
  diagonalHamiltonian_analytic_of G6031.1 (G6027 1 le_rfl).2.1

end
end NlsGge.ThirdConsultation.G6041S

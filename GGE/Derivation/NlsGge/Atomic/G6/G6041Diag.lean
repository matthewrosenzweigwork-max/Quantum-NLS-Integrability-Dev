import Mathlib
import NlsGge.Atomic.G6.G6041DiagCore
import NlsGge.Atomic.G6.G6031
import NlsGge.Atomic.G6.G6027

/- G6041 DIAG PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6041Diag.lean.
   SUPPORT glue (no packet increment): real analyticity of the actual diagonal Hamiltonian, discharging
   G6041S.diagonalHamiltonian_analytic_of with the landed G6031.1 and (G6027 1 le_rfl).2.1.
   ROOT MAIN PROBE (imports main-only G6031/G6027).  Own imports: Mathlib, G6041DiagCore, G6031, G6027. -/
set_option autoImplicit false

open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6041S
noncomputable section

theorem diagonalHamiltonian_analytic : AnalyticOnNhd ℝ diagonalHamiltonian Set.univ :=
  diagonalHamiltonian_analytic_of G6031.1 (G6027 1 le_rfl).2.1

end
end NlsGge.ThirdConsultation.G6041S

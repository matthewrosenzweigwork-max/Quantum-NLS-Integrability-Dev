import Mathlib
import NlsGge.GK38.ActionGradient

                                                                                                          
                                                                                              
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.ActionGradient

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G2_029 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    CircleIntegrable (gradRootQuotient φ) (discC φ n) (discR φ n) ∧
    HasFDerivAt (fun ψ : PotPair => gkActionC38 ψ n)
      (-(1/(Real.pi : ℂ)) • circleIntegral (gradRootQuotient φ)
        (discC φ n) (discR φ n)) φ ∧
    (∀ h : PotPair,
      CircleIntegrable (fun z => gradDiscrimCLM φ z h/canonRoot38 φ z)
        (discC φ n) (discR φ n)) :=
  ⟨actionGradient_integrable φ hφ n, action_hasFDeriv φ hφ n,
    fun h => gradRootQuotient_direction_circle_integrable φ hφ _ _
      (isolating_family38 φ hφ) n h⟩


end
end NlsGge.GKDefinitionDesign

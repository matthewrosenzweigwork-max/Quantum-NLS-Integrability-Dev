import Mathlib
import NlsGge.Atomic.G6.G6035Host

                                                                                                                          
                                                                                              
                                                                                              
                                                                                      
                                                                                           
set_option autoImplicit false

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Local real analytic extension to the ambient action Banach space. -/
def AnalyticAtCone (f : PositiveActionSpace → ℝ) (I : PositiveActionSpace) : Prop :=
  ∃ (U : Set WeightedActionSpace) (g : WeightedActionSpace → ℝ),
    IsOpen U ∧ I.val ∈ U ∧ AnalyticOnNhd ℝ g U ∧
    ∀ J : PositiveActionSpace, J.val ∈ U → g J.val = f J

end
end NlsGge.GKDefinitionDesign

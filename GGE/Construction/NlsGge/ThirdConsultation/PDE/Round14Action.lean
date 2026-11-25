import Mathlib
import NlsGge.Atomic.G6.G6035Host

                                                                                
                                                                                                                      
                                                                                                                         
                                                                                                                   
                                                                                                                  
                                                                                                                        
                                                                                                         
                                                               
                                                              
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

/-- Raw, unscaled actions; the topology used for differentiation is G6's lp1. -/
def positiveActionCone : Set (ℤ → ℝ) :=
  {I | (∀ n : ℤ, 0 ≤ I n) ∧
    Summable (fun n : ℤ => actionWeight n * I n)}

def actionCoe (I : PositiveActionSpace) : ℤ → ℝ :=
  fun n : ℤ => actionCoefficient I.val n

def actionNorm (I : WeightedActionSpace) : ℝ := ‖I‖

def actionNormBorel : MeasurableSpace PositiveActionSpace := borel _

def actionProductBorel : MeasurableSpace (ℤ → ℝ) := borel _

def LocalActionExtension (F : WeightedActionSpace → ℝ)
    (I : PositiveActionSpace) : Prop :=
  ∃ U : Set WeightedActionSpace,
    IsOpen U ∧ I.val ∈ U ∧ AnalyticOnNhd ℝ F U ∧
    ∀ J : PositiveActionSpace, J.val ∈ U → F J.val = actionHamiltonian J

end
end NlsGge.ThirdConsultation.PDE

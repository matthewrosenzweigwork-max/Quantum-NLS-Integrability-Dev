import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14ActionRaw
import NlsGge.Atomic.G6.G6041

                                                                                    
                                                                                                                        
                                                                                                                      
                                                                                                               
                                                                                                             
                                                                                                                          
                                                                              
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem actionExtension_exists (I : PositiveActionSpace) :
  ∃ F : WeightedActionSpace → ℝ, LocalActionExtension F I := by
  obtain ⟨U, g, hU, hI, ha, hag⟩ := G6041 I
  exact ⟨g, U, hU, hI, ha, hag⟩

def chosenActionExtension (I : PositiveActionSpace) : WeightedActionSpace → ℝ :=
  Classical.choose (actionExtension_exists I)

theorem chosenActionExtension_spec (I : PositiveActionSpace) :
  LocalActionExtension (chosenActionExtension I) I :=
  Classical.choose_spec (actionExtension_exists I)

/-- Derivative in the raw action, although lp1 stores a_n=w_n I_n. -/
def actionFrequency (n : ℤ) (I : PositiveActionSpace) : ℝ :=
  actionWeight n *
    fderiv ℝ (chosenActionExtension I) I.val (lp.single 1 n (1 : ℝ))

open scoped Classical in
/-- One fixed total family; outside the genuine action cone it is zero. -/
def actualOmega (n : ℤ) (I : ℤ → ℝ) : ℝ :=
  if hI : I ∈ positiveActionCone then
    actionFrequency n (rawActionToPositive I hI)
  else 0

end
end NlsGge.ThirdConsultation.PDE

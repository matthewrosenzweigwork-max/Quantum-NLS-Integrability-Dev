import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14ActionFreq
import NlsGge.ThirdConsultation.PDE.PDE061Core

                                                                                                                
                                                                                                                
                                                                                                               
                                                                                                                       
                                                                                                       
                                                  
set_option autoImplicit false
open MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE

theorem exists_measurable_actual_frequencies :
  ∃ Omega : ℤ → (ℤ → ℝ) → ℝ,
    Omega = actualOmega ∧ (∀ n : ℤ, Measurable (Omega n)) ∧
    ∀ (I : ℤ → ℝ) (hI : I ∈ positiveActionCone) (n : ℤ),
      Omega n I = actionFrequency n (rawActionToPositive I hI) :=
  ⟨actualOmega, rfl,
    fun n => measurable_omega_of chosenActionExtension chosenActionExtension_spec n,
    fun I hI n => by unfold actualOmega; rw [dif_pos hI]⟩

theorem measurable_actualOmega (n : ℤ) : Measurable (actualOmega n) :=
  measurable_omega_of chosenActionExtension chosenActionExtension_spec n

end NlsGge.ThirdConsultation.PDE

import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14ActionFreq
import NlsGge.ThirdConsultation.PDE.PDE061Core

/- PDE061 PRODUCTION01 (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/PDE/PDE061.lean, namespace
   NlsGge.ThirdConsultation.PDE. PDE-061: extend local analytic frequencies measurably to every action sequence.
   Head VERBATIM from Pro round 14 ('### PDE-061'; rounds 15/16 print no change). Opens reduced to the closure.
   Proof: PDE061Core.measurable_omega_of with ch := chosenActionExtension (chosenActionExtension_spec); actualOmega and
   actionFrequency unfold definitionally to the core's function (same classical decidability instance).
   MAIN-ONLY (Round14ActionFreq imports G6041). -/
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

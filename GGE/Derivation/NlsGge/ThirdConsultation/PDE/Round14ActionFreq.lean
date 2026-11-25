import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14ActionRaw
import NlsGge.Atomic.G6.G6041

/- PDEACTFREQ HOST PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target
   NlsGge/ThirdConsultation/PDE/Round14ActionFreq.lean, namespace NlsGge.ThirdConsultation.PDE. Bodies VERBATIM from the
   Pro r14 shared PDE block (l.2718-2736): actionExtension_exists (theorem obligation; proved from landed G6041, whose
   AnalyticAtCone actionHamiltonian I unpacks to ∃ g, LocalActionExtension g I — Pro r14 l.2597 "G6041 supplies
   actionExtension_exists"), chosenActionExtension, chosenActionExtension_spec, actionFrequency, actualOmega.
   LEXICAL REPAIR: `open scoped Classical in` before actualOmega (its `if hI : I ∈ positiveActionCone` needs decidability;
   the printed block has no classical instance). MAIN-ONLY (G6041 closure). -/
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

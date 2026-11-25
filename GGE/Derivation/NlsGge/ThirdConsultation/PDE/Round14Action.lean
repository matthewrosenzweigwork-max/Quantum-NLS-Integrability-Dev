import Mathlib
import NlsGge.Atomic.G6.G6035Host

/- PDEACT HOST PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target
   NlsGge/ThirdConsultation/PDE/Round14Action.lean, namespace NlsGge.ThirdConsultation.PDE (root/integrator to place).
   Bodies VERBATIM from PRO_DEFINITION_RESPONSE_FP80_14.md shared PDE block (l.2689-2716): positiveActionCone, actionCoe,
   actionNorm, actionNormBorel, actionProductBorel, LocalActionExtension. Only what PDE-059/PDE-060 need is hosted:
   rawAction_scaled_mem / rawActionToPositive / actionExtension_exists / chosenActionExtension / actionFrequency /
   actualOmega / rotation* (same block) are left to their consumers (PDE-061..). DT0/DPhi/omegaSeq of the same block are
   in the landed Round14Deriv. PositiveActionSpace, WeightedActionSpace, actionWeight, actionCoefficient,
   actionHamiltonian are the landed G6034Host/G6035Host owners.
   grep NlsGge/ (2026-11-02): none of the six names exists. -/
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

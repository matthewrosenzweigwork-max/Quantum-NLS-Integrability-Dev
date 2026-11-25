import Mathlib
import NlsGge.Atomic.G6.G6035Host

/- G6040 HOST PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6040Host.lean.
   Hosts ONCE the G6-040/041 head vocabulary AnalyticAtCone, body byte-identical to followup13
   DEFINITIONS/G6.lean.md:250-254 (doc comment included), namespace NlsGge.GKDefinitionDesign.
   PositiveActionSpace / actionHamiltonian: G6035Host; WeightedActionSpace: G6034Host.
   grep NlsGge/ (2026-11-02): the name does not exist.  Own imports: Mathlib, G6035Host. -/
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

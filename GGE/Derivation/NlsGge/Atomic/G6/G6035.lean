import Mathlib
import NlsGge.Atomic.G6.G6035Core
import NlsGge.Atomic.G6.G6033
import NlsGge.Atomic.G6.G6034

/- G6035 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6035.lean.
   Packet G6-035, head VERBATIM from Pro (followup13 STATEMENTS/G6.md §G6-035; round 15 Q5 "Retain exact head";
   pin cc702018); shared G6 context block.  Proof: G6035S.G6035_of applied to G6033.2.  TASK_INDEX prerequisites
   G6-033, G6-034 (G6-034's host names are used; the G6-034 theorem is imported for the dependency edge).
   BLOCKED until G6-033 (hence G6-032) lands.  No new hypothesis. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6035 :
  (∀ I : PositiveActionSpace,
    coordinateActionsPositive (positiveActionRoot I) = I ∧
    ‖positiveActionRoot I‖^2 = weightedActionNorm I.val) ∧
  (∀ z : SobolevCarrier38 ((1 : ℕ) : ℝ),
    transformedNLSHamiltonian z = actionHamiltonian (coordinateActionsPositive z)) ∧
  (∀ (I : PositiveActionSpace) (z : SobolevCarrier38 ((1 : ℕ) : ℝ)),
    coordinateActionsPositive z = I → transformedNLSHamiltonian z = actionHamiltonian I) :=
  NlsGge.ThirdConsultation.G6035S.G6035_of G6033.2

end
end NlsGge.GKDefinitionDesign

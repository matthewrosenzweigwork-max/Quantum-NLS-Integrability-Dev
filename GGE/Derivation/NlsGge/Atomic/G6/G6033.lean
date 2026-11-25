import Mathlib
import NlsGge.Atomic.G6.G6033Core
import NlsGge.Atomic.G6.G6031
import NlsGge.Atomic.G6.G6027
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6021
import NlsGge.Atomic.G6.G6032
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompat

/- G6033 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6033.lean.
   Packet G6-033, head VERBATIM from Pro (followup13 STATEMENTS/G6.md §G6-033; round 15 Q5 "Retain exact head";
   pin cc702018) up to the LEXICAL/ELABORATION REPAIR of landed G6-034 (round-14 cluster 12):
   `carrierCoe38 1 z` -> `carrierCoe38 ((1 : ℕ) : ℝ) z` (and w); the printed form does not elaborate
   (worker-lane request b99703e3).  Shared G6 context block (opens, namespace NlsGge.GKDefinitionDesign).
   Proof: G6033S.G6033_of applied to G6031.1, (G6027 1 le_rfl).2.1, inverseBirkhoffSobolev_embed 1,
   G6013 conjuncts 5/6, (G6021 u).2 and G6032.  TASK_INDEX prerequisites G6-027, G6-021, G6-031, G6-032.
   BLOCKED until G6-032 lands (see G6032_STOP.md).  No new hypothesis. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6033 :
  AnalyticOnNhd ℝ transformedNLSHamiltonian Set.univ ∧
  ∀ z w : SobolevCarrier38 ((1 : ℕ) : ℝ),
    (∀ n : ℤ, ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2 = ‖carrierCoe38 ((1 : ℕ) : ℝ) w n‖^2) →
    transformedNLSHamiltonian z = transformedNLSHamiltonian w :=
  NlsGge.ThirdConsultation.G6033S.G6033_of G6031.1 (G6027 1 le_rfl).2.1 (inverseBirkhoffSobolev_embed 1)
    G6013.2.2.2.2.1 G6013.2.2.2.2.2 (fun u => (G6021 u).2) (fun u v hiso => G6032 u v hiso)

end
end NlsGge.GKDefinitionDesign

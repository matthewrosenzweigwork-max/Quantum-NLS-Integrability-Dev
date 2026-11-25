import Mathlib
import NlsGge.Atomic.G6.G6041ConeCore
import NlsGge.Atomic.G6.G6041Diag
import NlsGge.Atomic.G6.G6041DiagLeaf
import NlsGge.Atomic.G6.G6033
import NlsGge.Atomic.G6.G6036Core

/- G6041 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6041.lean.
   Packet G6-041, head VERBATIM from Pro (followup13 STATEMENTS/G6.md; round 15 Q5 / round 16 §Q3 "retain the
   G6-040 and G6-041 target heads"); shared G6 context block.  Proof: G6041S.cone_of (G6041ConeCore; Pro r16 §Q3
   common-neighbourhood order L987-998) applied to G6041S.diagonalHamiltonian_analytic (G6041Diag),
   G6036S.diagH_flip G6033.2, and the landed h782 leaf diagonalHamiltonian_eq_actionHamiltonian (G6041DiagLeaf).
   TASK_INDEX prerequisites G6-040, G6-033, LIB-003 (G6-040 is a special case of the same core; G6-033 via
   diagH_flip; LIB-003 window convergence via Mathlib lp.hasSum_single in the core).
   ROOT MAIN PROBE.  No new hypothesis. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6041 (I : PositiveActionSpace) : AnalyticAtCone actionHamiltonian I :=
  NlsGge.ThirdConsultation.G6041S.cone_of NlsGge.ThirdConsultation.G6041S.diagonalHamiltonian_analytic
    (fun n x => NlsGge.ThirdConsultation.G6036S.diagH_flip G6033.2 n x)
    diagonalHamiltonian_eq_actionHamiltonian I

end
end NlsGge.GKDefinitionDesign

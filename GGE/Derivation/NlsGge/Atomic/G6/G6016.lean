import Mathlib
import NlsGge.Atomic.G6.G6016Host
import NlsGge.Atomic.G6.G6016Sup1Core
import NlsGge.Atomic.G6.G6016Sup2
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6014

/- G6-016 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).  Target NlsGge/Atomic/G6/G6016.lean.
   Head `G6016` VERBATIM from followup12 STATEMENTS/G6.md "## G6-016" (round 14: no change); G6 shared opens; no lexical repair.
   Proof (GK Theorem 20.1, first step): G6016Aux.core16 with G6016Sup2 (dPhi X_{I_n} = -i Phi_n e_n from the canonical
   relations G5-040 and I_n = |Phi_n|^2), the physical inverse equations of G6-013 and the analytic inverse of G6-014.
   TASK_INDEX prerequisite G5-026 is not consumed (the coordinate-gradient route of G6001 replaces the angle derivative). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6016 (n : ℤ) (u : PhysicalL2) :
  (fun t : ℝ => physicalInverseBirkhoff
    (rotateOneCoordinate n t (physicalBirkhoff u))) 0 = u ∧
  ∀ t : ℝ, HasDerivAt
    (fun s : ℝ => physicalInverseBirkhoff
      (rotateOneCoordinate n s (physicalBirkhoff u)))
    (physicalHamiltonianField (fun v => actualGapActionAllE02_38 v n)
      (physicalInverseBirkhoff (rotateOneCoordinate n t (physicalBirkhoff u)))) t :=
  G6016Aux.core16 fderiv_physicalBirkhoff_actionField G6013.2.2.2.2.1 G6013.2.2.2.2.2
    G6014.2.2.2.1 n u

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.Atomic.G6.G6011Sup1Core
import NlsGge.Atomic.G6.G6003
import NlsGge.Atomic.G6.G6009

/- G6-011 PACKET (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6011.lean.
   Head `G6011` VERBATIM from followup12 STATEMENTS/G6.md "## G6-011" (round 14 row: retain the existing complete head); G6 shared
   opens. No lexical repair.  Proof (GK Theorem 19.3, "X is closed"): G6011Aux.singletonFiber_isClosed (G6011Sup1Core) with
   properness G6009.1 and the local analytic inverse charts G6003. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6011 :
  IsClosed {z : CartesianReal | ∃! u : PhysicalL2, realBirkhoffCartesian u = z} := by
  exact G6011Aux.singletonFiber_isClosed realBirkhoffCartesian G6009.1 G6003

end
end NlsGge.GKDefinitionDesign

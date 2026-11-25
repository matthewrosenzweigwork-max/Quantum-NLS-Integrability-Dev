import Mathlib
import NlsGge.Atomic.G6.G6016Host
import NlsGge.Atomic.G6.G6017Sup1Core
import NlsGge.Atomic.G6.G6016

/- G6-017 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).  Target NlsGge/Atomic/G6/G6017.lean.
   Head `G6017` VERBATIM from followup12 STATEMENTS/G6.md "## G6-017" (already uses `lam`, round-14 cluster 12 rename);
   G6 shared opens; no lexical repair.  Proof (GK Theorem 20.1): G6017Aux.core17 with the G6-016 head; core17 uses
   G1-069 and G2-029 directly ({Delta(lam), I_n} = 0 by the G5-017 contour argument). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6017 (u : PhysicalL2) (n : ℤ) (t : ℝ) :
  let v := physicalInverseBirkhoff (rotateOneCoordinate n t (physicalBirkhoff u))
  (∀ lam : ℂ, discrim (realSlice v) lam = discrim (realSlice u) lam) ∧
  v ∈ isospectralSet u :=
  G6017Aux.core17 G6016 u n t

end
end NlsGge.GKDefinitionDesign

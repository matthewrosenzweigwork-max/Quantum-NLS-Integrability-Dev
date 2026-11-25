import Mathlib
import NlsGge.Atomic.G5.G5029
import NlsGge.Atomic.G5.G5020
import NlsGge.Atomic.G5.G5030Sup1Core

/- G5-030 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5030.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G5030` VERBATIM from followup12 STATEMENTS/G5.md section G5-030 (retained by round 14 cluster 5).  No lexical repair.
   Proof: G5030Sup1Aux.g5030_core (worker-lane compiled) with h29 := G5029 and hbeta := the HasSum clause of landed G5020 at the
   real slice (realSlice u ∈ sourceBetaW by sourceFamily.V_real, as in landed G5025).  Needs a root main probe (G5029 closure). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5030 (u : PhysicalL2) (m n : ℤ) (hleft : AllDirichletLeft u)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) :
  anglePoisson m n (realSlice u) = 0 :=
  G5030Sup1Aux.g5030_core G5029
    (fun v j => by
      obtain ⟨V, hV, -, -, hsum, -⟩ :=
        G5020 j (realSlice v) (sourceFamily.V_real (Set.mem_range_self v))
      exact hsum (realSlice v) (mem_of_mem_nhds hV))
    u m n hleft hm hn

end
end NlsGge.GKDefinitionDesign

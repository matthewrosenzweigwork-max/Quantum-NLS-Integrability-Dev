import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5035Sup2
import NlsGge.Atomic.G5.G5037
import NlsGge.Atomic.G5.G5038Sup1
import NlsGge.Atomic.G5.G5038Sup2

/- G5-038 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5038.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G5038` VERBATIM from followup12 STATEMENTS/G5.md section G5-038 (retained by round 14 cluster 5).  No lexical repair.
   Proof: the glue recorded in proof development G5038_STOP.md: G5038Sup1.core38 (proof development kit, worker-lane compiled by proof development)
   with hprim := landed G5035Sup2.angle_local_primitive, hdense := finiteGap_seq_tendsto u (G5038Sup2; L2 finite-gap density from
   landed KST-066 at Sobolev level 0, the input of DM-065), h37 := G5037.  Needs a root main probe. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5038 (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) :
  anglePoisson m n (realSlice u) = 0 :=
  G5038Sup1.core38 u m n hm hn G5035Sup2.angle_local_primitive (finiteGap_seq_tendsto u)
    (fun v m' n' h hm' hn' => G5037 v m' n' h hm' hn')

end
end NlsGge.GKDefinitionDesign

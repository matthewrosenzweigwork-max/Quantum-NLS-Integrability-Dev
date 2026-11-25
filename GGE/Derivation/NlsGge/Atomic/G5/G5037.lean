import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5030
import NlsGge.Atomic.G5.G5037Sup1
import NlsGge.ThirdConsultation.KO.Basic

/- G5-037 PACKET (proof development, AUTHOR; integrated unchanged by proof development; not self-reviewed, not accepted).
   G5030 is now supplied by proof development's kit (G5030_PRODUCTION01, head VERBATIM followup12 G5-030).
   Target NlsGge/Atomic/G5/G5037.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G5037` VERBATIM from followup12 STATEMENTS/G5.md section G5-037 except the lexical qualification
   `finiteGap` -> `NlsGge.ThirdConsultation.finiteGap` (round 14 cluster 12: "One finiteGap ... G5/G6/M imports/open use the canonical
   fully qualified name"; the proposed GKDefinitionDesign duplicate is removed).
   Proof: G5037Sup1.core37 with h30 := G5030 (whose type must be the VERBATIM followup12 G5030 head). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5037 (u : PhysicalL2) (m n : ℤ) (hfg : NlsGge.ThirdConsultation.finiteGap u)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) :
  anglePoisson m n (realSlice u) = 0 :=
  G5037Sup1.core37 u m n hfg hm hn (fun v m' n' hleft hm' hn' => G5030 v m' n' hleft hm' hn')

end
end NlsGge.GKDefinitionDesign

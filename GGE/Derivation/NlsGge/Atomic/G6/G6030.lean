import Mathlib
import NlsGge.Atomic.G6.G6030Core
import NlsGge.Atomic.G6.G6029
import NlsGge.Atomic.G6.G6027
import NlsGge.Atomic.G6.G6014
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompat

/- G6030 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6030.lean.
   Packet G6-030, head VERBATIM from Pro (followup13 STATEMENTS/G6.md §G6-030; round 15 Q5 "Retain exact head";
   pin cc702018), shared G6 context block as G6029 (opens, `open NlsGge.ThirdConsultation (finiteGap)`, namespace
   NlsGge.GKDefinitionDesign).  Proof: G6030S.G6030_of applied to G6029 clause 3, the landed birkhoffSobolev_coe,
   inverseBirkhoffSobolev_embed, birkhoffSobolev_inverse_compatible_all (LeftInverse), and G6030S.inv_continuous from
   G6014 (analytic physicalInverseBirkhoff, for m = 0) and G6027 (analytic inverseBirkhoffSobolev m, for 1 ≤ m).
   TASK_INDEX prerequisites G6-027, G6-029, LIB-003 (tendsto_projC38).  No new hypothesis; no repair. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace
open NlsGge.ThirdConsultation (finiteGap)

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6030 (u : PhysicalL2) (m : ℕ)
    (hu : fourierSeq38 u ∈ seqSobolev38 (m : ℝ)) :
  (∀ N : ℕ, finiteGap (finiteGapTruncation N u) ∧
    ∀ k : ℕ, fourierSeq38 (finiteGapTruncation N u) ∈ seqSobolev38 (k : ℝ)) ∧
  (∀ N : ℕ, physicalSobolevEmbed m (finiteGapTruncationSobolev m N u) =
    finiteGapTruncation N u) ∧
  Tendsto (fun N : ℕ => finiteGapTruncationSobolev m N u) atTop
    (𝓝 (physicalSobolevRecover m u)) :=
  NlsGge.ThirdConsultation.G6030S.G6030_of u m hu (G6029 u).2.2 (birkhoffSobolev_coe m)
    (inverseBirkhoffSobolev_embed m) (birkhoffSobolev_inverse_compatible_all m).1
    (NlsGge.ThirdConsultation.G6030S.inv_continuous m G6014.2.2.2.1 (fun hm => (G6027 m hm).2.1))

end
end NlsGge.GKDefinitionDesign

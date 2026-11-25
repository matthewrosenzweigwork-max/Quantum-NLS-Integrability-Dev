import Mathlib
import NlsGge.Atomic.G6.G6024
import NlsGge.Atomic.G6.G6026SupCore
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompat
import NlsGge.Atomic.KSN.KSN019
import NlsGge.Atomic.KSN.KSN001Sup1
import NlsGge.Atomic.G6.G6014
import NlsGge.Atomic.G6.G6002

/- G6027 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6027.lean.
   Packet G6-027, head VERBATIM from Pro (followup13 STATEMENTS/G6.md; round 15 "retain every G6-024..043 target head",
   source hypothesis 1 ≤ m kept; request pin cc702018); shared context block of that file (opens, namespace
   NlsGge.GKDefinitionDesign, noncomputable section). Producer order per Pro r15 Q6: KSN-019 → G6-024/025 → G6-026/027.
   Proof: NlsGge.ThirdConsultation.G6024S cores applied to the landed birkhoffSobolev_mem/_coe/_inverse_compatible_all
   (SobolevBirkhoffCompat), KSN001Aux.scalarBirkhoff_realSlice, KSN019_main m hm, G6014 (physicalBirkhoff analytic), G6002 (L² derivative isomorphism). No new hypothesis; no repair. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6027 (m : ℕ) (hm : 1 ≤ m) :
  AnalyticOnNhd ℝ (birkhoffSobolev m) Set.univ ∧
  AnalyticOnNhd ℝ (inverseBirkhoffSobolev m) Set.univ ∧
  Function.LeftInverse (inverseBirkhoffSobolev m) (birkhoffSobolev m) ∧
  Function.RightInverse (inverseBirkhoffSobolev m) (birkhoffSobolev m) ∧
  (∀ u : PhysicalSobolev38 (m : ℝ),
    (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ) ∧
    sequenceSobolevEmbed m (birkhoffSobolev m u) =
      physicalBirkhoff (physicalSobolevEmbed m u)) ∧
  (∀ z : SobolevCarrier38 (m : ℝ),
    fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbed m z)) ∈
      seqSobolev38 (m : ℝ) ∧
    physicalSobolevEmbed m (inverseBirkhoffSobolev m z) =
      physicalInverseBirkhoff (sequenceSobolevEmbed m z)) :=
  ⟨(G6024 m hm).2,
    NlsGge.ThirdConsultation.G6024S.inverse_analytic_of m (birkhoffSobolev_mem m) NlsGge.ThirdConsultation.KSN.KSN001Aux.scalarBirkhoff_realSlice
    (KSN019_main m hm).1 (fun x hx => ((KSN019_main m hm).2.1 x hx).1)
      (birkhoffSobolev_coe m) G6014.2.2.1 (fun v => (G6002 v).1)
      (birkhoffSobolev_inverse_compatible_all m).1 (birkhoffSobolev_inverse_compatible_all m).2.1,
    (birkhoffSobolev_inverse_compatible_all m).1, (birkhoffSobolev_inverse_compatible_all m).2.1,
    (birkhoffSobolev_inverse_compatible_all m).2.2.1, (birkhoffSobolev_inverse_compatible_all m).2.2.2⟩

end
end NlsGge.GKDefinitionDesign

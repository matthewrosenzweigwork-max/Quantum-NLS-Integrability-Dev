import Mathlib
import NlsGge.Atomic.G6.G6024Sup2Core
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompat
import NlsGge.Atomic.KSN.KSN019
import NlsGge.Atomic.KSN.KSN001Sup1

/- G6024 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6024.lean.
   Packet G6-024, head VERBATIM from Pro (followup13 STATEMENTS/G6.md; round 15 "retain every G6-024..043 target head",
   source hypothesis 1 ≤ m kept; request pin cc702018); shared context block of that file (opens, namespace
   NlsGge.GKDefinitionDesign, noncomputable section). Producer order per Pro r15 Q6: KSN-019 → G6-024/025 → G6-026/027.
   Proof: NlsGge.ThirdConsultation.G6024S cores applied to the landed birkhoffSobolev_mem/_coe/_inverse_compatible_all
   (SobolevBirkhoffCompat), KSN001Aux.scalarBirkhoff_realSlice, KSN019_main m hm. No new hypothesis; no repair. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6024 (m : ℕ) (hm : 1 ≤ m) :
  (∀ u : PhysicalSobolev38 (m : ℝ),
    (physicalBirkhoff (physicalSobolevEmbed m u) : ℤ → ℂ) ∈ seqSobolev38 (m : ℝ) ∧
    sequenceSobolevEmbed m (birkhoffSobolev m u) =
      physicalBirkhoff (physicalSobolevEmbed m u)) ∧
  AnalyticOnNhd ℝ (birkhoffSobolev m) Set.univ :=
  ⟨fun u => ⟨birkhoffSobolev_mem m u, birkhoffSobolev_coe m u⟩,
    NlsGge.ThirdConsultation.G6024S.birkhoffSobolev_analytic_of m (birkhoffSobolev_mem m) NlsGge.ThirdConsultation.KSN.KSN001Aux.scalarBirkhoff_realSlice
    (KSN019_main m hm).1 (fun x hx => ((KSN019_main m hm).2.1 x hx).1)⟩

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS015Host
import NlsGge.ThirdConsultation.KSPS.KSPS020Host
import NlsGge.ThirdConsultation.KSPS.KSPS023Host

/- KSPS-029 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS029Host.lean.
   Bodies VERBATIM from the round-14 active page followup12 DEFINITIONS/KSPS.lean.md, "Retained design-only bodies":
   `NlsGge.ThirdConsultation.KSPS.LpSequence`, `...KSPS.WeightedSquareSummable`, `...KSPS.gap` (Pro round 14 Cluster 1:
   retained bodies are hosted once). grep of NlsGge/ (2026-11-01): none of the three exists in namespace
   NlsGge.ThirdConsultation.KSPS (different, unrelated `NlsGge.Pilot.WeightedSquareSummable` and
   `NlsGge.GKDefinitionDesign.gap` exist; Pro: KSPS-029 does not use the Pilot one). LpSequence is consumed by KSPS-028.
   Header opens = Pro's block for those bodies (as KSPS023Host). No repair. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common NlsGge.ThirdConsultation
open NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def LpSequence (p : ℝ) (e : ℤ → ℂ) : Prop :=
  Summable (fun n : ℤ => ‖e n‖^p)

end
end NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def WeightedSquareSummable (s : ℝ) (e : ℤ → ℂ) : Prop :=
  WeightedL2Error s e

end
end NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def gap {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  periodicPlus φ n - periodicMinus φ n

end
end NlsGge.ThirdConsultation.KSPS

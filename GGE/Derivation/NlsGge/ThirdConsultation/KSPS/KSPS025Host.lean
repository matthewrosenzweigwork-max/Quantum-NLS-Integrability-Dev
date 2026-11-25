import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS020Host
import NlsGge.ThirdConsultation.KSPS.KSPS023Host

/- KSPS-025 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS025Host.lean.
   Body VERBATIM from the round-14 active page followup12 DEFINITIONS/KSPS.lean.md, "Retained design-only bodies"
   (`NlsGge.ThirdConsultation.KSPS.midpoint`; Pro round 14 Cluster 1: retained bodies are hosted once; KSPS-025
   "unchanged"). grep of NlsGge/ and Work/isolated_20261027 (2026-11-01): no `NlsGge.ThirdConsultation.KSPS.midpoint`
   (Mathlib's root `midpoint` is a different declaration; inside this namespace the KSPS name is used).
   Header opens = Pro's block for those bodies (as KSPS023Host). Uses KSPS020Host (periodicMinus, periodicPlus); KSPS023Host is imported only so that the Pro header namespaces exist.
   No repair. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common NlsGge.ThirdConsultation
open NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def midpoint {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  (periodicMinus φ n + periodicPlus φ n) / 2

end
end NlsGge.ThirdConsultation.KSPS

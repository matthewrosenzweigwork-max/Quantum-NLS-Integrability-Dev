import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.ThirdConsultation.KSPSInversePhaseHost
import NlsGge.GK38.PairRealBridge

/- KSPS-023 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS023Host.lean.
   Body VERBATIM from the round-14 active page followup12 DEFINITIONS/KSPS.lean.md, "Retained design-only bodies"
   (`NlsGge.ThirdConsultation.KSPS.spectralPolynomial`; Pro round 14 Cluster 1: these "are hosted once with their
   existing bodies"; KSPS-023 "unchanged"). grep of NlsGge/ and Work/isolated_20261027 (2026-11-01) found no
   `spectralPolynomial`. Header opens = Pro's block for those bodies (as KSPS015Host). No repair. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common NlsGge.ThirdConsultation
open NlsGge.ThirdConsultation.KSPSRiccati

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def spectralPolynomial {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  (n:ℂ)*Real.pi +
    ∑ k ∈ Finset.Icc 1 (N+1),
      NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k /
        (n:ℂ)^k

end
end NlsGge.ThirdConsultation.KSPS

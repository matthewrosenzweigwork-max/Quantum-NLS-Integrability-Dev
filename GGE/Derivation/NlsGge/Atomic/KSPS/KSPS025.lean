import Mathlib
import NlsGge.Atomic.KSPS.KSPS020
import NlsGge.Atomic.KSPS.KSPS024
import NlsGge.Atomic.KSPS.KSPS026
import NlsGge.Atomic.G1.G1054
import NlsGge.ThirdConsultation.KSPS.KSPS025Support

/- KSPS-025 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/KSPS/KSPS025.lean.
   Head: followup12 STATEMENTS/KSPS.md "KSPS-025 -- midpoint expansion" (Pro round 14 Cluster 1 audit-F2 row: "KSPS-025 ...
   unchanged"), theorem `midpoint_spectral_expansion`, VERBATIM.
   Proof: KSPS025W.midpoint_spectral_expansion_of, whose four explicit hypotheses are discharged by the landed heads
   rough_periodic_endpoints (KSPS-020), endpoint_quadratic_expansion (KSPS-026), G1054_main (G1-054) and the KSPS-024 head
   critical_spectral_expansion. No hypothesis added. Route deviation (G1-054 + KSPS-026 instead of G2-026 + M-032,
   which hold only on gkW): KSPS025_ROUTE.md. NOT COMPILED IN THE WORKER LANE (closure exceeds the lane memory cap):
   READY FOR ROOT MAIN PROBE; the identical term is compiled against the landed head TYPES in KSPS025_GLUETEST01. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem midpoint_spectral_expansion
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) :
  WeightedL2Error (N+1)
    (fun n => midpoint φ n - spectralPolynomial φ n) :=
  NlsGge.ThirdConsultation.KSPS025W.midpoint_spectral_expansion_of N hN φ
    rough_periodic_endpoints (endpoint_quadratic_expansion N hN φ)
    NlsGge.Atomic.G1054S3.Final.G1054_main
    (critical_spectral_expansion N hN φ)

end
end NlsGge.ThirdConsultation.KSPS

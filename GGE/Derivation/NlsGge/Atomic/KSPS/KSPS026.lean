import Mathlib
import NlsGge.Atomic.KSPS.KSPS011
import NlsGge.Atomic.KSPS.KSPS012
import NlsGge.Atomic.KSPS.KSPS013
import NlsGge.Atomic.KSPS.KSPS014
import NlsGge.Atomic.KSPS.KSPS015
import NlsGge.Atomic.KSPS.KSPS020
import NlsGge.ThirdConsultation.KSPS.KSPS026Support6

/- KSPS-026 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/KSPS/KSPS026.lean.
   Head: Pro round 14 (PRO_DEFINITION_RESPONSE_FP80_14.md, Cluster 1, "KSPS-026 -- exact endpoint phase quadratic with
   controlled coefficients" = followup12 STATEMENTS/KSPS.md), theorem `endpoint_quadratic_expansion`, VERBATIM.
   Proof: KSPS026Support6.endpoint_quadratic_expansion_of, whose six explicit hypotheses are discharged here by the
   landed heads WKB_endpoint_offdiagonal (KSPS-011), WKB_endpoint_diagonal (KSPS-012), integrated_riccati_vanishing
   (KSPS-013), WKB_monodromy_entries (KSPS-014, B = sobolevNorm N φ), rough_periodic_endpoints (KSPS-020) and the
   KSPS-015 head discriminant_WKB_sequence (kit proof development, under review). No hypothesis added. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem endpoint_quadratic_expansion
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) :
    EndpointQuadraticWKB N φ :=
  NlsGge.ThirdConsultation.KSPS026W.endpoint_quadratic_expansion_of N hN φ
    (fun xi hxi => WKB_endpoint_offdiagonal N hN φ xi hxi)
    (fun xi hxi => WKB_endpoint_diagonal N hN φ xi hxi)
    (fun k hk => integrated_riccati_vanishing N k φ hk)
    (fun lam hlam => (WKB_monodromy_entries N (sobolevNorm N φ) φ lam le_rfl hlam).2)
    (fun xi hxi => discriminant_WKB_sequence N hN φ xi hxi)
    rough_periodic_endpoints

end
end NlsGge.ThirdConsultation.KSPS

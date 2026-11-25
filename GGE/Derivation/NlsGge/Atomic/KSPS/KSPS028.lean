import Mathlib
import NlsGge.Atomic.KSPS.KSPS020
import NlsGge.Atomic.KSPS.KSPS025
import NlsGge.Atomic.KSPS.KSPS026
import NlsGge.ThirdConsultation.KSPS.KSPS028Support
import NlsGge.ThirdConsultation.KSPS.KSPS028Support2
import NlsGge.ThirdConsultation.M.M053Host

/- KSPS-028 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/KSPS/KSPS028.lean.
   Head: followup12 STATEMENTS/KSPS.md "KSPS-028 -- real endpoint expansion with l4 remainder" (Pro round 14 Cluster 1:
   unchanged), theorem `real_periodic_endpoint_expansion`, VERBATIM except the binder repair of OWNER DECISION 18
   (root AUDIT_DEFERRED_NOTES01.md; evidence proof development/ISREALTYPE_RULING.md):
   `(hφ : IsRealType (toPotPair φ))` -> `(hφ : NlsGge.ThirdConsultation.MRiccati.RealPair φ)` (corrected_target binder
   repair; import M053Host). `physicalFourier` read with Pro's fragment open `NlsGge.Pilot` (lexical, as KSPS-023).
   Proof: KSPS028W.real_periodic_endpoint_expansion_of over the landed heads rough_periodic_endpoints (KSPS-020),
   endpoint_quadratic_expansion (KSPS-026), midpoint_spectral_expansion (KSPS-025) and KSPS028Q.real_facts (from hφ).
   No hypothesis added. ROOT MAIN PROBE (the glue module exceeds the worker-lane memory cap). -/
set_option autoImplicit false
open NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem real_periodic_endpoint_expansion
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N)
    (hφ : NlsGge.ThirdConsultation.MRiccati.RealPair φ) :
  ∃ eplus eminus : ℤ → ℂ,
    LpSequence 4 eplus ∧ LpSequence 4 eminus ∧
    ∀ n : ℤ, n ≠ 0 →
      periodicPlus φ n =
        spectralPolynomial φ n +
          ‖physicalFourier (toPotPair φ).1 (-n)‖ +
          eplus n / indexValue n^(N+1) ∧
      periodicMinus φ n =
        spectralPolynomial φ n -
          ‖physicalFourier (toPotPair φ).1 (-n)‖ +
          eminus n / indexValue n^(N+1) :=
  NlsGge.ThirdConsultation.KSPS028W.real_periodic_endpoint_expansion_of N hN φ
    rough_periodic_endpoints (endpoint_quadratic_expansion N hN φ) (midpoint_spectral_expansion N hN φ)
    (NlsGge.ThirdConsultation.KSPS028Q.real_facts φ hφ).1 (NlsGge.ThirdConsultation.KSPS028Q.real_facts φ hφ).2

end
end NlsGge.ThirdConsultation.KSPS

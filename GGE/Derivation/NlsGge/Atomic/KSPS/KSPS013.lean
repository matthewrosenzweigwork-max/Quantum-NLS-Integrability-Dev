import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Host
import NlsGge.ThirdConsultation.KSPS.KSPS013Support

/- KSPS-013 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/KSPS/KSPS013.lean.
   Head: Pro round 14 (PRO_DEFINITION_RESPONSE_FP80_14.md, Cluster 1, "KSPS-013 -- equality of integrated Riccati
   coefficients" = followup12 STATEMENTS/KSPS.md), theorem `integrated_riccati_vanishing`, VERBATIM.
   integralRiccatiRight is the KSPS-012 host body (Pro round 14, literal). Route: KSPS013_ROUTE.md
   (k = 1 directly for every N; 2 <= k <= N+1 by the formal Riccati Wronskian identity + formal-log exactness +
   H^1 realisation; see KSPS013Support). -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem integrated_riccati_vanishing
    (N k : ℕ) (φ : SobolevC N)
    (hk : 1 ≤ k ∧ k ≤ N + 1) :
    integralRiccatiLeft φ k = integralRiccatiRight φ k := by
  obtain ⟨hk1, hkN⟩ := hk
  unfold integralRiccatiRight
  by_cases h1 : k = 1
  · subst h1
    exact NlsGge.ThirdConsultation.KSPSWKB.rv_vanishing_one φ
  · exact NlsGge.ThirdConsultation.KSPSWKB.rv_vanishing_ge_two φ k (by omega) hkN

end
end NlsGge.ThirdConsultation.KSPS

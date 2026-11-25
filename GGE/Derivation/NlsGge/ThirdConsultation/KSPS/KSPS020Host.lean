import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.GK38.PeriodicLabellingCanonical

/- KSPS-020 HOST01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS020Host.lean.
   The two bodies are the design declarations `periodicMinus` and `periodicPlus` of DEFINITIONS/KSPS.lean.md (identical text
   in followup5..10, namespace NlsGge.ThirdConsultation.KSPS, binders {N : ℕ} (φ : SobolevC N) (n : ℤ)), VERBATIM:
   they call `NlsGge.GK38.lamMinus` / `NlsGge.GK38.lamPlus`, which exist (PeriodicLabellingCanonical). No repair. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def periodicMinus {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  NlsGge.GK38.lamMinus (toPotPair φ) n

def periodicPlus {N : ℕ} (φ : SobolevC N) (n : ℤ) : ℂ :=
  NlsGge.GK38.lamPlus (toPotPair φ) n

end
end NlsGge.ThirdConsultation.KSPS

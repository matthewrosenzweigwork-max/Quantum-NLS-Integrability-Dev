import Mathlib
import NlsGge.ThirdConsultation.KSPSInversePhaseHost

/- M-053 alias host (proof development, AUTHOR; not reviewed).
   Target NlsGge/ThirdConsultation/KSPSCoefficientHost.lean.
   Verbatim Pro round 13 section 9 / KSPS.lean.md alias; name grep-checked absent from NlsGge/. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

def integralRiccatiCoefficient := @integralRiccatiLeft

end
end NlsGge.ThirdConsultation.KSPS

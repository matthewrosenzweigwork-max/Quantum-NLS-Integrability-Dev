import Mathlib
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.KST.KST013

/- KST052Host PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST052Host.lean.
   SUPPORTING host module (no packet increment).  Body VERBATIM from the design DEFINITIONS/KST.lean.md
   (gpt6pro_followup10, line 481; Pro rounds 7-12 do not touch it): eigenspace (kernel of the actual unbounded
   KST013.dirac minus z times the domain inclusion).  Not defined anywhere in NlsGge (grep) nor in another worker's
   candidate (grep).  `Potential` is the landed NlsGge.ThirdConsultation.KST.Potential (DM004); `dirac` is the landed
   NlsGge.Atomic.KST013.dirac (opened exactly as in the design header). -/
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST013

namespace NlsGge.ThirdConsultation.KST

def eigenspace (φ : Potential) (z : ℂ) : Submodule ℂ (dirac φ).domain :=
  LinearMap.ker ((dirac φ).toFun - z • (dirac φ).domain.subtype)

end NlsGge.ThirdConsultation.KST
end

import Mathlib
import NlsGge.GK38.Lib.InterpolationHilbertOp

/- COMMONACT HOST PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/Common/Actions.lean,
   namespace NlsGge.ThirdConsultation.Common (the namespace of the landed COMMON FiniteSupportSequence host,
   NlsGge/ThirdConsultation/Common/FiniteSupport.lean).  Body VERBATIM from followup13 DEFINITIONS/COMMON.lean.md
   l.130-131.  ROOT LEXICAL REPAIR 22 (as landed FiniteSupportSequence and BirkhoffRaw actualPhi): binder type
   `NlsGge.Birkhoff.Lib.L2Z` -> `NlsGge.GK38.Lib.L2Z` (only the latter exists).  grep NlsGge/ (2026-11-02): no
   declaration named `actions`.  Consumers: Pro r14 rotationSequence/rotationDerivativeSequence (PDE-063..). -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.Common
noncomputable section

def actions (z : NlsGge.GK38.Lib.L2Z) (n : ℤ) : ℝ :=
  ‖z n‖^2

end
end NlsGge.ThirdConsultation.Common

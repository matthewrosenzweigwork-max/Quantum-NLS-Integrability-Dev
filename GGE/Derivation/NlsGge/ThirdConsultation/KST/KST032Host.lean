import Mathlib
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.DM.DM004

/- KST032Host PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST032Host.lean.
   SUPPORTING host module (no packet increment).  Body VERBATIM from the design DEFINITIONS/KST.lean.md
   (gpt6pro_followup10, line 417; Pro rounds 7-12 do not change it): diagonalZero.  It is not defined anywhere in
   NlsGge (grep) and not in any other worker's candidate (grep).  `center`, `a`, `Potential` are the landed
   NlsGge.ThirdConsultation.KST declarations (KST018 / DM004 via KST016).
   LEXICAL REPAIR (elaboration only): attribute [local instance] Classical.propDecidable for the dite
   (same repair as KST031Host). -/
set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

def diagonalZero (n : ℤ) (φ : Potential) : ℂ :=
  if h : ∃ z : ℂ, z ∈ Metric.closedBall (center n) (Real.pi/48) ∧
      z = center n + a φ n z then Classical.choose h else center n

end NlsGge.ThirdConsultation.KST
end

import Mathlib
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST027
import NlsGge.ThirdConsultation.KST.KST034Host

/- KST062Host HOST01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST062Host.lean.
   SUPPORTING host module (no packet increment).  Owner: KST-062 (the only packet listed for these two objects in
   OBJECT_TABLE.json).  Bodies VERBATIM from the design DEFINITIONS/KST.lean.md (truncateCoefficients :468,
   truncateWeighted :471; identical in gpt6pro_followup9/10; no Pro round 11-12 entry touches them).  Neither is
   defined anywhere in NlsGge (grep) nor in another worker's folder (grep).  Already landed and imported, NOT
   redeclared: RawPair / weightedCoeffs / weightedLift (KST034Host), Weighted / weightFact (KST027).
   No lexical repair. -/
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

def truncateCoefficients (J : ℕ) (r : RawPair) : RawPair :=
  fun channel m => if m.natAbs ≤ J then r channel m else 0

def truncateWeighted (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (J : ℕ) (x : Weighted ω) : Weighted ω :=
  weightedLift ω (truncateCoefficients J (weightedCoeffs ω x))

end NlsGge.ThirdConsultation.KST
end

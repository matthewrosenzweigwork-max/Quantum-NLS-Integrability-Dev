import Mathlib
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST027
import NlsGge.ThirdConsultation.KST.KST034Host

/- KST040Host HOST01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST040Host.lean.
   SUPPORTING host module (no packet increment).  Bodies VERBATIM from the design DEFINITIONS/KST.lean.md
   (:460 coefficientInvolution, :463 weightedInvolution; identical in gpt6pro_followup8/9/10; no Pro round
   11-12 entry touches them).  Neither is defined anywhere in NlsGge (grep) nor in another worker's candidate (grep).
   Already landed and imported, NOT redeclared: RawPair / weightedCoeffs / weightedLift (KST034Host), Weighted /
   weightFact (KST027).  `adaptedInverse` is NOT declared here: its single host is proof development's KST039Host. -/
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

def coefficientInvolution (ε : ℝ) (r : RawPair) : RawPair :=
  fun channel m => (ε : ℂ) * star (r (!channel) (-m))

def weightedInvolution (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (ε : ℝ) (x : Weighted ω) : Weighted ω :=
  weightedLift ω (coefficientInvolution ε (weightedCoeffs ω x))

end NlsGge.ThirdConsultation.KST
end

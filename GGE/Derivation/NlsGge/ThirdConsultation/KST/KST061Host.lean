import Mathlib
import NlsGge.Atomic.KST.KST059
import NlsGge.ThirdConsultation.KST.KST034Host

/- KST061Host PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST061Host.lean.
   SUPPORTING host module (no packet increment).  Bodies VERBATIM from the design DEFINITIONS/KST.lean.md
   (gpt6pro_followup10; Pro rounds 7-12 do not touch them): FiniteFourierSupport (:476, KST namespace; the DM
   namespace has its own FiniteFourierSupport from Pro round 12 -- different full name, never open both namespaces),
   pairFiniteGap (:196).  Neither is defined in the KST namespace in NlsGge (grep) nor in another worker's candidate.
   LEXICAL REPAIR (elaboration only): `actualGapSequence` in pairFiniteGap is the landed
   NlsGge.Atomic.KST059.actualGapSequence (body lamPlus - lamMinus, PeriodicPair = PotPair; same body as the design's
   actualGapSequence), selectively opened as in the landed KST052 precedent. -/
set_option autoImplicit false
noncomputable section
open NlsGge.GK38
open NlsGge.Atomic.KST059 (actualGapSequence)

namespace NlsGge.ThirdConsultation.KST

def FiniteFourierSupport (J : ℕ) (r : RawPair) : Prop :=
  ∀ channel m, J < m.natAbs → r channel m = 0

def pairFiniteGap (φ : PotPair) : Prop :=
  {n : ℤ | actualGapSequence φ n ≠ 0}.Finite

end NlsGge.ThirdConsultation.KST
end

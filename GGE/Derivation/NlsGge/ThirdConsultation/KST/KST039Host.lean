import Mathlib
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST027
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST034Host

/- KST039Host HOST01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST039Host.lean.
   SUPPORTING host module (no packet increment).  Owner: KST-039 (first packet in the OBJECT_TABLE list
   KST-039, KST-040, KST-062 for `adaptedInverse`); KST-040 / KST-062 import this module.
   Body VERBATIM from the design DEFINITIONS/KST.lean.md (:454; identical in gpt6pro_followup1/8/9/10; no Pro round
   7-12 entry touches it).  `adaptedInverse` is not defined anywhere in NlsGge (grep) nor in a landed host.
   Already landed, NOT redeclared: Weighted / weightFact (KST027), componentBall (KST033Host),
   adaptedFourier (KST034Host).
   LEXICAL REPAIR (elaboration only): attribute [local instance] Classical.propDecidable for the dite
   (same repair as KST035Host adaptedThreshold). -/
set_option autoImplicit false
noncomputable section
open NlsGge.GK38 NlsGge.Atomic.KST002 NlsGge.Pilot

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

def adaptedInverse (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (M : ℝ) (N : ℕ) (y : Weighted ω) : Weighted ω :=
  if h : ∃ x ∈ componentBall ω M, adaptedFourier ω hω N x = y
  then Classical.choose h else 0

end NlsGge.ThirdConsultation.KST
end

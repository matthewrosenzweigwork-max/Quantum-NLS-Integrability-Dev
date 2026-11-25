import Mathlib
import NlsGge.Atomic.DM.DM046
import NlsGge.Atomic.KST.KST043
import NlsGge.ThirdConsultation.KST.Basic

/- KST046Host HOST01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST046Host.lean.
   SUPPORTING host module (no packet increment).  Owner: KST-046 (first packet needing them).  Bodies VERBATIM
   from the design DEFINITIONS/KST.lean.md (identical in gpt6pro_followup7/8/9/10; Pro rounds 7-12 do not touch them):
   ExponentialWeight (:186), expWeight (:479).  Neither is defined anywhere in NlsGge (grep) nor in a landed host
   (grep `ExponentialWeight|expWeight` over NlsGge/ returns nothing).  Already landed, NOT redeclared:
   AdmissibleWeight (KST/Basic), SubmultiplicativeWeight (DM046), KSTLogRatio (KST043).
   No lexical repair: the bodies are the design text. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST043 NlsGge.Atomic.DM046

namespace NlsGge.ThirdConsultation.KST

def ExponentialWeight (ω : ℤ → ℝ) (χ : ℝ) : Prop :=
  AdmissibleWeight ω ∧ SubmultiplicativeWeight ω ∧ 0 < χ ∧
  Tendsto (KSTLogRatio ω) atTop (𝓝 χ)

def expWeight (ε : ℝ) (k : ℤ) : ℝ := Real.exp (ε * (k.natAbs : ℝ))

end NlsGge.ThirdConsultation.KST
end

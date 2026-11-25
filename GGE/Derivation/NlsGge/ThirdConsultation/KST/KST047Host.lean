import Mathlib
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST019

/- KST047Host PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST047Host.lean.
   SUPPORTING host module (no packet increment; also consumed by KST-048/049).  Bodies VERBATIM from the design
   DEFINITIONS/KST.lean.md (gpt6pro_followup10, lines 167-172; Pro rounds 7-12 do not touch them): Balanced,
   rootRadius.  Not defined anywhere in NlsGge (grep) nor in any other worker's candidate.  `SmallCoefficients` is the
   landed KST019 declaration, `center` the landed KST018 one.  No lexical repair. -/
set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.KST

def Balanced (n : ℤ) (a b c : ℂ → ℂ) (σ : ℂ) : Prop :=
  SmallCoefficients n a b c ∧ σ = center n + a σ ∧
  ‖σ - center n‖ ≤ Real.pi / 48 ∧ b σ * c σ ≠ 0 ∧
  (1 / 9 : ℝ) ≤ ‖c σ / b σ‖ ∧ ‖c σ / b σ‖ ≤ 9

def rootRadius (b c : ℂ → ℂ) (σ : ℂ) : ℝ := Real.sqrt ‖b σ * c σ‖

end NlsGge.ThirdConsultation.KST
end

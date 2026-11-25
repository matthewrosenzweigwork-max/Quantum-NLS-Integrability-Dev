import Mathlib
import NlsGge.Atomic.DM.DM046
import NlsGge.Atomic.M.M054

/- M022Host (proof development, AUTHOR; not self-reviewed). Single definition for the M-022 head, verbatim from
   Pro round 9 (PRO_DEFINITION_RESPONSE_FP80_09.md section 3; DEFINITIONS/M.lean.md followup7, `def OneDerivativeWeight`).
   Weight: w k = indexWeight k * v k with v even, v >= 1, submultiplicative; indexWeight j = 1 + |j| (M-054). -/

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M

def OneDerivativeWeight (w : ℤ → ℝ) : Prop :=
   ∃ v : ℤ → ℝ,
     (∀ k : ℤ, 1 ≤ v k) ∧
     (∀ k : ℤ, v (-k) = v k) ∧
     NlsGge.Atomic.DM046.SubmultiplicativeWeight v ∧
     (∀ k : ℤ,
       w k = NlsGge.Atomic.M.M054.indexWeight k * v k)

end NlsGge.ThirdConsultation.M

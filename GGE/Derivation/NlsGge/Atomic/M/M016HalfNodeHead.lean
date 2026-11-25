import Mathlib
import NlsGge.Atomic.M.M016HalfNode
import NlsGge.Atomic.M.M052

/- M016HALFNODEHEAD PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target NlsGge/Atomic/M/M016HalfNodeHead.lean.
   Needs ROOT MAIN PROBE (imports M052). Pro R16 §1.1 head VERBATIM
   (L95-106), in exactly the form consumed by proof development's KSPS031SharpLaurent. The R14 body of the representative is
   definitionally the hypothesis `hF` of `exterior_primitive_halfNode_eq_of_rep`. -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem exterior_primitive_halfNode_eq
    (N : ℕ) (φ : KSPS.SobolevC N) (R : ℝ) (F : ℂ → ℂ)
    (hF : ExteriorPrimitiveRepresentative (KSPS.toPotPair φ) R F)
    (hzero : MPrimitive.HasValueAtInfinity
      (fun z : ℂ => F z + Complex.I * z) 0) :
    ∃ J : ℕ, ∀ (j : ℤ) (hj : J ≤ j.natAbs),
      ∃ hchart : KSPSWKB.NonresonantBranchDomain φ j
        (KSPSWKB.halfNode j),
        F (KSPSWKB.halfNode j) = KSPSWKB.primitive N φ
          ⟨(j, KSPSWKB.halfNode j), hchart⟩ :=
  exterior_primitive_halfNode_eq_of_rep N φ R F hF hzero

end NlsGge.ThirdConsultation.M

import Mathlib
import NlsGge.Atomic.M.M016HalfNode
import NlsGge.Atomic.M.M052

                                                                                                                                               
                                                                   
                                                                                                                      
                                                                                    
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

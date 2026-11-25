import Mathlib
import NlsGge.Atomic.M.M051Host
import NlsGge.Atomic.M.M016DiscIdentity
import NlsGge.Atomic.M.M016HalfNodeCore
import NlsGge.ThirdConsultation.KSPS.KSPS031Host

                                                                                                     
                                                                                                                         
                                                                                                      
                                                                                                          
                                                                                                                    
                                                                                                        
                                                                                           
                                                                                                             
                                                                                                                  

set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem exterior_primitive_halfNode_eq_of_rep
    (N : ℕ) (φ : KSPS.SobolevC N) (R : ℝ) (F : ℂ → ℂ)
    (hF : 0 < R ∧ ∀ z : ℂ, R < ‖z‖ →
      ∃ hz : KSPS.toPotPair φ ∈ gkW ∧ z ∈ MPrimitive.endpointClosureFiber (KSPS.toPotPair φ),
        F z = primitive ⟨(KSPS.toPotPair φ, z), hz⟩)
    (hzero : MPrimitive.HasValueAtInfinity
      (fun z : ℂ => F z + Complex.I * z) 0) :
    ∃ J : ℕ, ∀ (j : ℤ) (hj : J ≤ j.natAbs),
      ∃ hchart : KSPSWKB.NonresonantBranchDomain φ j
        (KSPSWKB.halfNode j),
        F (KSPSWKB.halfNode j) = KSPSWKB.primitive N φ
          ⟨(j, KSPSWKB.halfNode j), hchart⟩ := by
  have hcosh : ∀ z : ℂ, R < ‖z‖ → 2 * Complex.cosh (F z) = KSPS.discriminant φ z := by
    intro z hz
    obtain ⟨hz', e⟩ := hF.2 z hz
    rw [e]
    exact primitive_discriminant_identity (KSPS.toPotPair φ) hz'.1 z hz'.2
  obtain ⟨J, hJ⟩ := M016ChartAux.halfNode_generic F (KSPS.discriminant φ) R hcosh hzero
  refine ⟨J, fun j hj => ?_⟩
  obtain ⟨-, hD, hFeq⟩ := hJ j hj
  have hchart : KSPSWKB.NonresonantBranchDomain φ j (KSPSWKB.halfNode j) := by
    refine ⟨?_, hD⟩
    rw [sub_self, norm_zero]
    positivity
  exact ⟨hchart, hFeq⟩

end NlsGge.ThirdConsultation.M

import Mathlib
import NlsGge.Atomic.DM.DM046
import NlsGge.Atomic.M.M054

                                                                                                         
                                                                                                                          
                                                                                                                

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

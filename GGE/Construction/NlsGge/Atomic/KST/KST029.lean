import Mathlib
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST029Bridge

                                                                                                        
                                                                                             
                                                                                                 
                                                                                            
set_option autoImplicit false
open NlsGge.Atomic.KST004 NlsGge.GK38

namespace NlsGge.ThirdConsultation.KST
noncomputable section

theorem kst029 (φ0 : Potential) :
  ∃ e : ℝ, 0 < e ∧ ∃ N : ℕ, 5 ≤ N ∧
  ∀ φ : Potential, ‖φ-φ0‖ < e → ∀ n : ℤ, N ≤ n.natAbs →
    SmallCoefficients n (a φ n) (b φ n) (c φ n) ∧
    Lib.zeroMultiset (determinant n (a φ n) (b φ n) (c φ n))
      (Metric.ball (center n) (Real.pi/3)) =
      {lamMinus (periodicPair φ) n, lamPlus (periodicPair φ) n} ∧
    (∀ z ∈ spectralStrip n, determinant n (a φ n) (b φ n) (c φ n) z = 0 ↔
      z = lamMinus (periodicPair φ) n ∨ z = lamPlus (periodicPair φ) n) :=
  kst029_of_bridge operatorPerCharBridge φ0

end
end NlsGge.ThirdConsultation.KST

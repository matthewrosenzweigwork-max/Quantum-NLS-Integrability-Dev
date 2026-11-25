import Mathlib
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST029Bridge

/- KST-029 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST029.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head verbatim from STATEMENTS/KST.md `## KST-029`
   (Pro followup10, identical in followup1..10), proved from the supporting modules KST029Support
   (`kst029_of_bridge`, hosts `periodicPair`) and KST029Bridge (`operatorPerCharBridge`). -/
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

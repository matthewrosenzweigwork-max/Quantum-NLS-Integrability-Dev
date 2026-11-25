import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS014Support5

                                                                                                                            
                                                                                                                     
                                                                                        
                                                                                         
                                                                        
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section
open NlsGge.Pilot NlsGge.GK38

theorem WKB_monodromy_entries
    (N : ℕ) (B : ℝ) (φ : SobolevC N)
    (lam : {z : ℂ // z ≠ 0})
    (hB : sobolevNorm N φ ≤ B)
    (hlam : WKBThreshold N B lam.1) :
    (∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      (1 / 2 : ℝ) ≤ ‖Matrix.det (KSPSWKB.wkbColumns φ lam x)‖) ∧
    monodromyPair (toPotPair φ) lam.1 =
      KSPSWKB.explicitWKBMonodromy N φ lam :=
  KSPSWKB.WKB_monodromy_entries_of_column_identity N B φ lam hB hlam
    (wkbColumns_eq_fundPair_mul N φ lam)

end
end NlsGge.ThirdConsultation.KSPS

import Mathlib
import NlsGge.ThirdConsultation.M.M030Bridge
import NlsGge.ThirdConsultation.M.M031Weight
import NlsGge.ThirdConsultation.M.M031Energy
import NlsGge.ThirdConsultation.M.M031LowCore

   
                                                                                                             

                                                                                               
                                                                                    
                                        
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem low_label_re_bound (φ : KSPS.SobolevC 1) :
    let Q : ℝ := MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ)
    ∀ n : ℤ, NlsGge.Atomic.M.M054.indexWeight n < 8 * Q ^ 2 → ∀ plus : Bool,
      |(if plus then lamPlus (KSPS.toPotPair φ) n else lamMinus (KSPS.toPotPair φ) n).re| ≤
        (8 * Q ^ 2 - 1 / 2) * Real.pi :=
  low_label_re_bound_core sourceH1Weight oneDerivativeWeight_sourceH1Weight (KSPS.toPotPair φ)
    (sourceH1_energy_ne_top φ)
    (fun ψ hψ m hm z hz h0 =>
      perChar_zero_schurDet_zero sourceH1Weight oneDerivativeWeight_sourceH1Weight ψ hψ m hm z hz h0)

end NlsGge.ThirdConsultation.M

end

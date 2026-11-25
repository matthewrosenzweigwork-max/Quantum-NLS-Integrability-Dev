import Mathlib
import NlsGge.ThirdConsultation.M.M030Bridge
import NlsGge.ThirdConsultation.M.M031Weight
import NlsGge.ThirdConsultation.M.M031Energy

   
                                                                                                                              

                                                                                                        
                                                                                                       
                                                                                                            
                                                                                                              
                                                                                             
                                                              
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem periodic_spectral_localization_high
    (φ : KSPS.SobolevC 1) (hW : KSPS.toPotPair φ ∈ gkW) :
    let Q : ℝ := MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ)
    ∀ n : ℤ, 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n →
      ∀ plus : Bool,
        ‖(if plus then lamPlus (KSPS.toPotPair φ) n
          else lamMinus (KSPS.toPotPair φ) n) -
          (n : ℂ) * (Real.pi : ℂ)‖ ≤
          Q ^ 2 / NlsGge.Atomic.M.M054.indexWeight n +
            Real.sqrt 2 * Q / NlsGge.Atomic.M.M054.indexWeight (2 * n) := by
  intro Q n hn plus
  obtain ⟨_, _, hm, hp, _, _⟩ := periodic_labels_are_local_roots sourceH1Weight
    oneDerivativeWeight_sourceH1Weight (KSPS.toPotPair φ) hW (sourceH1_energy_ne_top φ) n hn
  cases plus
  · have h := Metric.mem_closedBall.1 hm
    rw [dist_eq_norm] at h
    simpa only [Bool.false_eq_true, ↓reduceIte] using h
  · have h := Metric.mem_closedBall.1 hp
    rw [dist_eq_norm] at h
    simpa only [↓reduceIte] using h

end NlsGge.ThirdConsultation.M

end

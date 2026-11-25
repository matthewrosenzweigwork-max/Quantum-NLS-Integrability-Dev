import Mathlib
import NlsGge.Atomic.M.M026
import NlsGge.ThirdConsultation.M.M028Host
import NlsGge.ThirdConsultation.M.MSchurBound

   
                                                                                           

                                                                                                                       
                                                                                                        
                                                                                          
                                                                                         
                                                                               
                                                                                                                 
                                                                                     
                                                                                                                  
                                                                                              
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

theorem schur_offdiagonal_bound
    (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair)
    (hφ :
      NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hthreshold :
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight n)
    (plus : Bool) :
    w (2 * n) *
        ‖NlsGge.ThirdConsultation.MTwoMode.offDiagonal φ n lam hlam plus -
          NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ plus
            (if plus then 2 * n else -2 * n)‖ ≤
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 *
        NlsGge.ThirdConsultation.M.componentNorm w φ plus /
          NlsGge.Atomic.M.M054.indexWeight n := by
  rw [schur_fourier_remainder_weighted w hw φ hφ n lam hlam hthreshold plus]
  exact NlsGge.ThirdConsultation.MTwoModeB.even_remainder_bound w hw φ hφ n lam hlam hthreshold plus

end NlsGge.ThirdConsultation.M

end

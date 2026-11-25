import Mathlib
import NlsGge.Atomic.M.M026
import NlsGge.ThirdConsultation.M.MSchurDiag

   
                                                                                      

                                                                                                                    
                                                                                                        
                                                                                                                    
                                                                                             
                                                                                                                     
                                                                                                                    
             
                                                                                                                    
                                                                                                                           
                                                                               
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

theorem schur_diagonal_bound
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
    ‖(if plus then
        NlsGge.ThirdConsultation.MTwoMode.schurDiagonalPlus φ n lam hlam
      else
        NlsGge.ThirdConsultation.MTwoMode.schurDiagonalMinus φ n lam hlam)‖ ≤
      NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 /
        NlsGge.Atomic.M.M054.indexWeight n := by
  have h := schur_diagonal_odd_formula_weighted w hw φ hφ n lam hlam hthreshold plus
  obtain ⟨h1, _⟩ := h
  rw [h1]
  exact NlsGge.ThirdConsultation.MTwoModeB.odd_remainder_bound w hw φ hφ n lam hlam hthreshold plus

end NlsGge.ThirdConsultation.M

end

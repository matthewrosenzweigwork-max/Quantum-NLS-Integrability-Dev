import Mathlib
import NlsGge.Birkhoff.S04Moments38

                                                                                                                    
                                                                               
                                                                                      
                                                                                                                           
                                                                                                           
                                                                                                    
                                                                                                                 
                                                                                                                  
set_option autoImplicit false
open MeasureTheory NlsGge.Measure
open scoped ENNReal
noncomputable section

namespace NlsGge.Birkhoff

def nuHatDens38 (B : BirkhoffTop38) (c : ℕ → ℝ) (Λ : Finset ℤ) (w : Λ → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (B.densΛ38 c Λ w / B.ZcalΛ38 c Λ)

theorem nuHat38_eq_withDensity_nuHatDens38 (B : BirkhoffTop38) (c : ℕ → ℝ) (Λ : Finset ℤ) :
    B.nuHat38 c Λ = (finiteComplexVolume Λ).withDensity (nuHatDens38 B c Λ) := rfl

end NlsGge.Birkhoff

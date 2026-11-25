import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS006Host

                                                                                                              
                                                                                                                
                                                                                                                  
                                                                                                              
                                                             
                                                                                                                            
                                                                                                                      
                                                                                                                 
                                                                                                                   
                                                                                                                  
set_option autoImplicit false

open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section

def supMatrixDerivativeError (j : Fin 3) (φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1) (lam : ℂ) : ℝ :=
  ⨆ x : Set.Icc (0 : ℝ) 1,
    ‖iteratedDeriv (j : ℕ)
        (fun l : ℂ => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ (x : ℝ) l) lam -
      iteratedDeriv (j : ℕ)
        (fun l : ℂ => NlsGge.ThirdConsultation.KSPS.freePropagator (x : ℝ) l) lam‖

end
end NlsGge.ThirdConsultation.KSPSWKB

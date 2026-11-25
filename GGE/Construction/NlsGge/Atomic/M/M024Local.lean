import Mathlib
import NlsGge.ThirdConsultation.M.MRound11Host
import NlsGge.ThirdConsultation.M.MRound11Elim
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST013

   
                                                                                                  
                                        

                                                                                                         
                                                                                                            
                                                                                                         
                                                                                                  
                                                   

                                                                                                   
                                                                                    
                                                                 
                                                           
                                                              
                                                          
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

theorem eigenvalue_iff_schur_det_zero
    (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hsmall :
      ‖NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam ^ 2‖ ≤
        (1 / 2 : ℝ)) :
    NlsGge.ThirdConsultation.MTwoMode.PeriodicEigenvalue φ n lam ↔
      Matrix.det
        (NlsGge.ThirdConsultation.MTwoMode.schurMatrix φ n lam hlam) = 0 :=
  NlsGge.ThirdConsultation.MTwoModeSupp.periodicEigenvalue_iff_det_core
    NlsGge.Atomic.KST013.stage13AC_actual_proper_operator_graph_iff
    NlsGge.Atomic.KST013.stage13G_projection_zero_forces_zero
    NlsGge.Atomic.KST013.stage13K_actual_forward_reduced_formula
    NlsGge.Atomic.KST012.stageD_reconstructed_actual_bridges
    φ n lam hlam hsmall

end NlsGge.ThirdConsultation.M

end

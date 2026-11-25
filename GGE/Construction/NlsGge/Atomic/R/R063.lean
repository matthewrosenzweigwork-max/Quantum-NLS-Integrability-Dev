                                                                                                                                                                                                                                          
                                                                    
import NlsGge.Birkhoff.F01Determinant38c

                                                                                                         
                                                                                                                 
                                                                                                                               
                                                                                                       
                                                                     

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Analysis.RegularizedDeterminant
open NlsGge.Birkhoff

namespace NlsGge.Atomic.R

theorem norm_sq_ofCLM_le_h1h2_38 (A : H0_38 →L[ℝ] H0_38) (D D' : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ, A (i10_38 ξ) = i20_38 (D ξ))
    (hD' : ∀ ξ, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (D' ξ)) :
    ‖HilbertSchmidt.ofCLM A (isHilbertSchmidt_of_h1h2_38 A D D' hD hD')‖ ^ 2 ≤
      (‖D‖ ^ 2 + ‖D'‖ ^ 2) * hsConst38 :=
  NlsGge.Birkhoff.norm_sq_ofCLM_le_h1h2_38 A D D' hD hD'


end NlsGge.Atomic.R

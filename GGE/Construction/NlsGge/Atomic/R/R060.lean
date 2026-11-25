import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.Birkhoff.F01Determinant38c

                                                                                                              
                                                                                       
                                                                                                                     
                                                                                                    
                                                                                                                       
                                                                                  
                                                                                                      
                                                                                                                       
                                                                                
set_option autoImplicit false
open NlsGge.Sobolev38 NlsGge.Birkhoff
namespace NlsGge.ThirdConsultation.R

theorem r060_main (x : H0_38) :
    ContinuousLinearMap.adjoint (PDE.actualBirkhoffInput38.Bop x) =
      -(J38 ((0 : ℕ) : ℝ) *
        (PDE.actualBirkhoffInput38.Linv x - 1) *
        J38 ((0 : ℕ) : ℝ)) :=
  NlsGge.Birkhoff.BirkhoffInput38.Bop_adjoint
    PDE.actualBirkhoffInput38 x

end NlsGge.ThirdConsultation.R

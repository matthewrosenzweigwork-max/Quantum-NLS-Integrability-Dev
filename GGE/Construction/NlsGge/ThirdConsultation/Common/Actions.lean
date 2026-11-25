import Mathlib
import NlsGge.GK38.Lib.InterpolationHilbertOp

                                                                                                                        
                                                                                                            
                                                                                                                 
                                                                                                              
                                                                                                              
                                                                                                               
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.Common
noncomputable section

def actions (z : NlsGge.GK38.Lib.L2Z) (n : ℤ) : ℝ :=
  ‖z n‖^2

end
end NlsGge.ThirdConsultation.Common

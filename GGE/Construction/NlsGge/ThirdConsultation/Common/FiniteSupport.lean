import Mathlib
import NlsGge.GK38.Lib.InterpolationHilbertOp

                                                                                   
                                                                                                                           
                                                                                                    
                                                                                                                            
                                                                                                                       
                                                                                                                   
                                                                                                             
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.Common

/-- Finite support in the integer coordinate sequence. -/
def FiniteSupportSequence (z : NlsGge.GK38.Lib.L2Z) : Prop :=
  {n : ℤ | z n ≠ 0}.Finite

end NlsGge.ThirdConsultation.Common

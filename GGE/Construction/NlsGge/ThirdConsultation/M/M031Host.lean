import Mathlib

   
                                                                                

                                                                                                            
                                                                                               
                                                                                          
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

/-- Source Sobolev weight evaluated at the raw doubled index. -/
def sourceH1Weight (k : ℤ) : ℝ := 1 + |Real.pi * (k : ℝ)|

end NlsGge.ThirdConsultation.M

end

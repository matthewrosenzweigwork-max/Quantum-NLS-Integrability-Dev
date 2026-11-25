import Mathlib
import NlsGge.Atomic.M.M009Support3
import NlsGge.Atomic.M.M009Support5

                                                                                                                   
                                                                                                                        
                                                                                                                   
                                                                                                                      
                                                                                                         
                                                                                                                      
                                                                                                                  
                                                                                               
                                                                                                                    
                                                                                                               
                                                                     
set_option autoImplicit false
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.MPrimitive

theorem cutFreeFiber_isPreconnected (φ : PotPair) (hφ : φ ∈ gkW) :
    IsPreconnected (NlsGge.ThirdConsultation.MPrimitive.cutFreeFiber φ) :=
  polygonal_isPreconnected (cutFreeFiber_polygonal φ hφ)

end NlsGge.ThirdConsultation.MPrimitive

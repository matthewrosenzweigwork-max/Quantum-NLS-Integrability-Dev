                                                                                                                                            
import Mathlib
import NlsGge.Birkhoff.S01Translation38

                                                                                                                        
                                                                                                                                 

set_option autoImplicit false
open NlsGge.Birkhoff NlsGge.Pilot

namespace NlsGge.ThirdConsultation.PDE

theorem translation_hasDerivAt {u w : PhysicalL2} {t0 : ℝ} (hw : IsFourierDeriv38 u w) :
    HasDerivAt (fun t => translateL2_38 t u) (translateL2_38 t0 w) t0 :=
  NlsGge.Birkhoff.hasDerivAt_translate38 hw t0

end NlsGge.ThirdConsultation.PDE

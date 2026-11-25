import Mathlib
import NlsGge.NLS38.LaxConsequences38

                                                                                                     
                                                                                                                                    
                                                                                                                              
                                                                                                                                         
                                                                                                         
set_option autoImplicit false
open NlsGge.Pilot NlsGge.NLS38

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

def actualHalfTrace (u : PhysicalL2) (z : ℂ) : ℂ :=
  NlsGge.SpectralFoundations.actualPhysicalUnitHalfTrace32 u z

theorem actual_halfTrace_h1_conserved {u : PhysicalL2}
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (t : ℝ) (z : ℂ) :
    actualHalfTrace (nlsFlowL2 t u) z = actualHalfTrace u z :=
  actualPhysicalUnitHalfTrace_nlsFlow_h1 u hu t z

end
end NlsGge.ThirdConsultation.PDE

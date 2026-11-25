import Mathlib
import NlsGge.NLS38.LaxConsequences38

                                                                                                                          
                                                                                                                    
                                                                                                                          
                                                                                                          
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem actual_full_energy_conserved {c : ℕ → ℝ} {u : PhysicalL2}
    (hu : SobolevSquareSummable 3 (physicalFourier u)) (t : ℝ) :
    energyW38 c (nlsFlowL2 t u) = energyW38 c u :=
  energyW38_nlsFlow c u hu t

end
end NlsGge.ThirdConsultation.PDE

                                                                                                      
                                                                                           
                                                       
import Mathlib
import NlsGge.NLS38.FlowMeasure38

set_option autoImplicit false
open NlsGge.NLS38 NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem measurable_actual_flow (t : ℝ) : Measurable (nlsFlowL2 t) :=
  measurable_nlsFlowL2 t

end
end NlsGge.ThirdConsultation.PDE

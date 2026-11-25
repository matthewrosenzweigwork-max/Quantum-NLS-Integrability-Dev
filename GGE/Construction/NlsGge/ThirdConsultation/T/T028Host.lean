import Mathlib
import NlsGge.ThirdConsultation.T.T027Host
import NlsGge.Birkhoff.S04Moments38d

                                                                                                             
                                                                                  
                                                                                         
                                                                                                               
                                                                                                                 
                                                                                                                   
                                                                                                                   
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.T
noncomputable section

def evenCharge (j : ℕ) (u : PhysicalL2) : ℝ :=
  chargeFn38 (max 2 (j + 1)) j u

end
end NlsGge.ThirdConsultation.T

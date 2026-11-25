import Mathlib
import NlsGge.ThirdConsultation.T.T026Host

                                                                                         
                                                                                  
                                                                                  
                                                                                                       
                                                                                                                   
                                                                                                                    
                                                                                                                   
                                                          
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.T
noncomputable section

-- This is the finite-energy E_s accessor only. The global energy is EB38.
def lowerEnergy {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (x : ECarrier38 c s) : ℝ :=
  (EB38 c.val (physicalInclusion c s x)).toReal

end
end NlsGge.ThirdConsultation.T

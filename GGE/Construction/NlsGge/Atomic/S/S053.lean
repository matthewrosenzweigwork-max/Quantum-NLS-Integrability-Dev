import Mathlib
import NlsGge.Hierarchy.UniformPartitionBoundAux38

                                                                                                                                                    
                                                                                                                                             
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.S

theorem fullEnergy_reserved_split {lo up : ℝ} (c : BoundedCoefficients lo up)
    (N : ℕ) (z : FourierPlane N) :
    fullEnergy38 c N z = fullEnergy38 (shiftedCoefficients38 c) N z +
      shiftEps38 lo up * reservedEnergy38 c N z :=
  fullEnergy38_split c N z

end NlsGge.ThirdConsultation.S

end

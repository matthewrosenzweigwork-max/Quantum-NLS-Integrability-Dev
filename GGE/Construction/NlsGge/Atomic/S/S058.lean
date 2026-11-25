import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Hierarchy.UniformPartitionBound38

                                                                                                          
                                                                                  
                                                                                                              
                               
                                                                                       
                                                                                                        
                                                                                                               
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur NlsGge.Measure NlsGge.SpectralFoundations
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.S

theorem uniformRelativePartition_bound (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : BoundedCoefficients lo up) (N : ℕ),
      relativePartition38 c N ≤ C :=
  uniformRelativePartition_bound38 lo up hl hlu

end NlsGge.ThirdConsultation.S

import Mathlib
import NlsGge.GK38.GradEigenClosedGeneric

                                                                                                     
                                                                                                 
                                                                                                         
                                                                                                          
                                                             

set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38.GradEigen38

namespace NlsGge.Atomic.G1066

theorem G1_066 :
    Dense {u : PhysicalL2 | ∀ n : ℤ,
      actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n} ∧
    IsGδ {u : PhysicalL2 | ∀ n : ℤ,
      actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n} := by
  refine ⟨all_gaps_generic_target, ?_⟩
  rw [all_gaps_open_eq_iInter]
  exact IsGδ.iInter_of_isOpen fun n => (closed_nowhere_dense_target n).2.2.1

end NlsGge.Atomic.G1066


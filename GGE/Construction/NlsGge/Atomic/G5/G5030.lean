import Mathlib
import NlsGge.Atomic.G5.G5029
import NlsGge.Atomic.G5.G5020
import NlsGge.Atomic.G5.G5030Sup1Core

                                                                        
                                                                           
                                                                                                                              
                                                                                                                                
                                                                                                                                  
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5030 (u : PhysicalL2) (m n : ℤ) (hleft : AllDirichletLeft u)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) :
  anglePoisson m n (realSlice u) = 0 :=
  G5030Sup1Aux.g5030_core G5029
    (fun v j => by
      obtain ⟨V, hV, -, -, hsum, -⟩ :=
        G5020 j (realSlice v) (sourceFamily.V_real (Set.mem_range_self v))
      exact hsum (realSlice v) (mem_of_mem_nhds hV))
    u m n hleft hm hn

end
end NlsGge.GKDefinitionDesign

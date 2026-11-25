import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5035Sup2
import NlsGge.Atomic.G5.G5037
import NlsGge.Atomic.G5.G5038Sup1
import NlsGge.Atomic.G5.G5038Sup2

                                                                        
                                                                           
                                                                                                                              
                                                                                                                                 
                                                                                                                                 
                                                                                                      
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5038 (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) :
  anglePoisson m n (realSlice u) = 0 :=
  G5038Sup1.core38 u m n hm hn G5035Sup2.angle_local_primitive (finiteGap_seq_tendsto u)
    (fun v m' n' h hm' hn' => G5037 v m' n' h hm' hn')

end
end NlsGge.GKDefinitionDesign

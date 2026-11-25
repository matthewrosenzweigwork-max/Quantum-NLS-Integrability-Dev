import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5035Sup1
import NlsGge.Atomic.G5.G5035Sup2
import NlsGge.Atomic.G5.G5025
import NlsGge.Atomic.G5.G5032
import NlsGge.Atomic.G5.G5034

                                                                        
                                                                           
                                                                                                                                  
                                                                                                                              
                                                                                                 
                                                                  
                                                                                                                              
                                                                                                                  
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5035 (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) :
  ∀ lam : ℂ, doubleAngleDiscriminantBracket m n (realSlice u) lam = 0 :=
  G5035Sup1.core35 u m n hm hn G5035Sup2.angle_local_primitive
    (fun w j hj => (G5025 w j hj).2) (G5032 u m n hm hn) (fun i j hi => G5034 u i j hi)

end
end NlsGge.GKDefinitionDesign

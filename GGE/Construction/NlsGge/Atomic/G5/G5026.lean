import Mathlib
import NlsGge.Atomic.G5.G5025
import NlsGge.Atomic.G2.G2075
import NlsGge.Atomic.G5.G5026Sup1

                                                                        
                                                                           
                                                                                                                               
                                                                                                                        
                                               
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5026 (u : PhysicalL2) (m n : ℤ)
    (hn : gamma2 (realSlice u) n ≠ 0) :
  pairPoissonCLM (angleDerivative n (realSlice u))
    (fderiv ℂ (fun φ => gkActionC38 φ m) (realSlice u)) =
      if m = n then 1 else 0 :=
  G5026Sup1.core26 u n m (G5025 u n hn).2
    (((G2_075.2.2.2.2.1 n (realSlice u) (sourceFamily.W_real (Set.mem_range_self u))).2.1 m).2)

end
end NlsGge.GKDefinitionDesign

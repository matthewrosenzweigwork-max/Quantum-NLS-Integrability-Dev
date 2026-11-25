import Mathlib
import NlsGge.Atomic.G1.G1082Sup3
import NlsGge.Atomic.G1.G1082Sup4

                                                                                                                                    
                                                                                                        
                                                                                                                          
                                                                                                    
                                                                                                                                                 
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G1_082 (n : ℤ) (u : PhysicalL2) :
    (∀ m : ℤ, m ≠ n → ∀ t : ℝ,
      gkMu (singleGapFlow n t u) m = gkMu u m) ∧
    (∀ t : ℝ,
      HasDerivAt (fun s : ℝ => gkMu (singleGapFlow n s u) n)
        (-(antiDiscrim (realSlice (singleGapFlow n t u))
          (gkMu (singleGapFlow n t u) n : ℂ)).re / 2) t) ∧
    (actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n →
      ∀ t : ℝ,
        HasDerivAt
          (fun s : ℝ => deriv (fun r : ℝ => gkMu (singleGapFlow n r u) n) s)
          ((discrim (realSlice u) (gkMu (singleGapFlow n t u) n : ℂ) *
            deriv (discrim (realSlice u))
              (gkMu (singleGapFlow n t u) n : ℂ)).re / 4) t ∧
        ((gkMu (singleGapFlow n t u) n = actualGapLowerAllE02_38 u n ∨
          gkMu (singleGapFlow n t u) n = actualGapUpperAllE02_38 u n) →
          deriv (deriv (fun r : ℝ => gkMu (singleGapFlow n r u) n)) t ≠ 0) ∧
        (actualGapLowerAllE02_38 u n < gkMu (singleGapFlow n t u) n →
          gkMu (singleGapFlow n t u) n < actualGapUpperAllE02_38 u n →
          deriv (fun r : ℝ => gkMu (singleGapFlow n r u) n) t ≠ 0)) :=
  NlsGge.Atomic.G1082Sup3.G1_082_of_witness n (NlsGge.Atomic.G1082Sup4.exists_deltaMu_ne_zero n) u

end
end NlsGge.GKDefinitionDesign

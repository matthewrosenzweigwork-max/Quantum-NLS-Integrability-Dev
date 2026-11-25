import Mathlib
import NlsGge.Atomic.G6.G6015

                                                                                                        
                                                                                                                                               
                                                                                                                                                        
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem isospectral_gapLevelSet_eq {u v : PhysicalL2} (h : isospectral u v) (n : ℤ) :
    actualGapLevelSetE02_38 v n = actualGapLevelSetE02_38 u n := by
  have hΔ := G6015Aux.halfTrace_eq_of_isospectral h
  have hp : actualQuasimomentumRealPartE02_38 v = actualQuasimomentumRealPartE02_38 u := by
    funext x
    simp only [actualQuasimomentumRealPartE02_38, G6015Aux.boundary_eq hΔ x]
  simp only [actualGapLevelSetE02_38, hp]

theorem isospectral_gapLower_eq {u v : PhysicalL2} (h : isospectral u v) (n : ℤ) :
    actualGapLowerAllE02_38 v n = actualGapLowerAllE02_38 u n := by
  simp only [actualGapLowerAllE02_38, isospectral_gapLevelSet_eq h n]

theorem isospectral_gapUpper_eq {u v : PhysicalL2} (h : isospectral u v) (n : ℤ) :
    actualGapUpperAllE02_38 v n = actualGapUpperAllE02_38 u n := by
  simp only [actualGapUpperAllE02_38, isospectral_gapLevelSet_eq h n]

end
end NlsGge.GKDefinitionDesign

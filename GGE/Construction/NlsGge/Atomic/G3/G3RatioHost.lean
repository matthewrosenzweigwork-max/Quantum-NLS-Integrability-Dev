import Mathlib
import NlsGge.Atomic.G3.G3019
import NlsGge.ThirdConsultation.G2.G2071Support1
import NlsGge.Atomic.G2.G2019

                                                                                                                         
                                                                                                    
                                                                     
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def betaRootRatioAlong (n m : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  (normalizedRoot n m φ - betaSegmentPoint m φ t) /
    standardRoot φ m (betaSegmentPoint m φ t)

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.Atomic.G3.G3SegmentHost

                                                                                                                  
                                                                                                    
                                                                                                                              
                                                                                         
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def betaInitialSegment (n m : ℤ) (φ : PotPair) (ε : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..ε, betaSegmentDensity n m φ t

end
end NlsGge.GKDefinitionDesign

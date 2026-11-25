import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G2.G2019

                                                                                                         
                                                                                              
                                                                                                      
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def finiteGapCuts (u : PhysicalL2) (S : Finset ℤ) : Set ℂ :=
  ⋃ n ∈ (S : Set ℤ), gapSegment (realSlice u) n

def finiteGapDifferential (u : PhysicalL2) (S : Finset ℤ) (z : ℂ) : ℂ :=
  -Complex.I * ∏ n ∈ S,
    (lamDot (realSlice u) n-z)/standardRoot (realSlice u) n z

end
end NlsGge.GKDefinitionDesign

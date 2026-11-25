import Mathlib
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.GK38.Lib.InterpolationTail

                                                                                                                          
                                                                                                                            
                                                                                                                           
                                                                                                                          
                                                                                                                   
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped Classical ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Symmetric truncation includes n=0 for every N. -/
def truncatePhysicalCoordinates (N : ℕ) (z : Lib.L2Z) : Lib.L2Z :=
  ∑ n ∈ Lib.win N, lp.single 2 n (z n)

def finiteGapTruncation (N : ℕ) (u : PhysicalL2) : PhysicalL2 :=
  physicalInverseBirkhoff (truncatePhysicalCoordinates N (physicalBirkhoff u))

end
end NlsGge.GKDefinitionDesign

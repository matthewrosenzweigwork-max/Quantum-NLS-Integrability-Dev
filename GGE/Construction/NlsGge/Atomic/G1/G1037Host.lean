import Mathlib
import NlsGge.Atomic.G1.G1036
import NlsGge.ThirdConsultation.G1.Round6

                                                                                             
                                                                                                 
                                                                                                           
                                                                                                    
                                                                   
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section

def wkbSigma (N : ℕ) (l : ℂ) (φ : PotPair) : ℂ :=
  -Complex.I*l - hierarchyHamiltonian 1 φ / (2*Complex.I*l) +
    ∑ k ∈ Finset.Icc 2 N, hierarchyHamiltonian k φ / (2*Complex.I*l)^k

end
end NlsGge.GKDefinitionDesign

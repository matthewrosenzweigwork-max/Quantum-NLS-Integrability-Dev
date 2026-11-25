import Mathlib
import NlsGge.Atomic.X.X006
import NlsGge.Atomic.G2.G2046
import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.PeriodicLabellingCanonical

                                                                                                                                                                  
                                                                                                                                                                                  
                                                                                       
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev sourceFamily :=
  NlsGge.Atomic.ExistingPhysicalFamily.actualPhysicalLocalFamily

def sourceW : Set PotPair := sourceFamily.W
def sourceF : (n : ℤ) → PotPair → P2Space38 n := sourceFamily.F
def sourceBetaW : Set PotPair := sourceFamily.V
def betaSum : ℤ → PotPair → ℂ := sourceFamily.beta

def collapsedSet (n : ℤ) : Set PotPair :=
  {φ | φ ∈ sourceW ∧ gamma2 φ n = 0}

def endpointSet (n : ℤ) : Set PotPair :=
  {φ | φ ∈ sourceW ∧ perChar φ (muSeq φ n) = 0}

end
end NlsGge.GKDefinitionDesign

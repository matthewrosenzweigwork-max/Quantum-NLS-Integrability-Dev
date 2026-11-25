import Mathlib
import NlsGge.Atomic.G4.G4017
import NlsGge.Atomic.G4.G4022Host
import NlsGge.Atomic.G4.G4036Host

                                                                                                               
                                                                                                                   
                                                                                                                  
                                                                                          
                                                                                          
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def collapsedZValue (n : ℤ) (a : ℤ) (φ : PotPair) : ℂ :=
  2 * (tauN φ n - muSeq φ n) * (1 + (a : ℂ) * sheetSign n φ) *
    Complex.exp (chi n φ)

end
end NlsGge.GKDefinitionDesign

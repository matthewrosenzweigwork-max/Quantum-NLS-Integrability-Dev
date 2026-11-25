import Mathlib
import NlsGge.Atomic.G4.G4027
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.TauGammaDefs

                                                                                                                                
                                                                                                                                   
                                                                                                                                           
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def elementaryEtaIntegral (n : ℤ) (φ : PotPair) : ℂ :=
  if lamPlus φ n = lamMinus φ n then 0
  else elementarySlitIntegral (lamPlus φ n - lamMinus φ n) (tauN φ n) (muSeq φ n)

end
end NlsGge.GKDefinitionDesign

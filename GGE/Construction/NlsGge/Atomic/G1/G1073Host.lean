import NlsGge.GK38.PairRealBridge

                                                                                                     
                                                                                              
                                                                                                                     
set_option autoImplicit false

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def simplePeriodic (φ : PotPair) (z : ℂ) : Prop :=
  perChar φ z = 0 ∧ deriv (perChar φ) z ≠ 0

end
end NlsGge.GKDefinitionDesign

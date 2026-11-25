import Mathlib
import NlsGge.ThirdConsultation.G5033Host

                                                                                                                
                                                                                                                
                                                                                                                              
                                                                                                                             
                                                                                                                                                 
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def pairGradient (f : PotPair → ℂ) (φ : PotPair) : PotPair :=
  pairGradientCLM (fderiv ℂ f φ)

def pairHamiltonianField (g : PotPair → ℂ) (φ : PotPair) : PotPair :=
  (-Complex.I • (pairGradient g φ).2, Complex.I • (pairGradient g φ).1)

def pairPoisson (f g : PotPair → ℂ) (φ : PotPair) : ℂ :=
  fderiv ℂ f φ (pairHamiltonianField g φ)

end
end NlsGge.GKDefinitionDesign

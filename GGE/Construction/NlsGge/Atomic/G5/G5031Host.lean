import Mathlib
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.Atomic.G5.G5017Host

                                                                                                              
                                                                                                                    
                                                                                                                                       
                                                                                                                              
                                                                                                             
                                                                                            
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def anglePoisson (m n : ℤ) (φ : PotPair) : ℂ :=
  pairPoissonCLM (angleDerivative m φ) (angleDerivative n φ)

def doubleAngleDiscriminantBracket (m n : ℤ) (φ : PotPair) (lam : ℂ) : ℂ :=
  pairPoisson (fun ψ => discrim ψ lam) (anglePoisson m n) φ

end
end NlsGge.GKDefinitionDesign

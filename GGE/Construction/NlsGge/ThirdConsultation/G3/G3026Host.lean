import Mathlib
import NlsGge.ThirdConsultation.G3.G3003Host
import NlsGge.GK38.Lib.EntireProductsC34b

                                                                              
                                                                                                                               
                                                                                                                                         
                                                                                                                                      
                                                                                                                                       
                                                                                  
                                                                                                             
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def fixedIndexReciprocalTail (n : ℤ) (R : ℕ) : ℝ :=
  Real.sqrt (∑' m : ℤ, if (R : ℝ) < |(m : ℝ)| then Lib.c3w n m ^ 2 else 0)

def betaPartialSum (n : ℤ) (R : ℕ) (φ : PotPair) : ℂ :=
  ∑ m ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), offDiagonalBeta n m φ

end
end NlsGge.GKDefinitionDesign

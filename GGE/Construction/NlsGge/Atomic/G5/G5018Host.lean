import Mathlib
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.ThirdConsultation.G3.G3003Host

                                                                                                                     
                                                                                                                          
                                                                                                                                 
                                                                                                                                  
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
noncomputable section

def beta (m n : ℤ) : PotPair → ℂ := offDiagonalBeta n m

def angleIntegralDerivative (m n : ℤ) (φ : PotPair) : PotPair →L[ℂ] ℂ :=
  if m = n then angleDerivative n φ - fderiv ℂ (betaSum n) φ
  else fderiv ℂ (beta m n) φ

end
end NlsGge.GKDefinitionDesign

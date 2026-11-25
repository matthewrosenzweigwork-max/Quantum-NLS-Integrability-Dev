import Mathlib
import NlsGge.GK38.Defs
import NlsGge.GK38.AbelianSpace
import NlsGge.GK38.Lib.EntireProductsParama
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import Armstrong.Work.ActualCartesianXYModels

                                                                                                             
                                                                                                               
                                                                                       
                                                                   
                                                                                                   
                                                                                                               
                                                                                                           
                                                                                                            
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- The bilinear, not Hermitian, L2 gradient of a complex functional. -/
def pairGradientCLM (L : PotPair →L[ℂ] ℂ) : PotPair :=
  (star ((InnerProductSpace.toDual ℂ PhysicalL2).symm
      (L.comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2))),
   star ((InnerProductSpace.toDual ℂ PhysicalL2).symm
      (L.comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2))))

def pairPoissonCLM (L M : PotPair →L[ℂ] ℂ) : ℂ :=
  L (-Complex.I • (pairGradientCLM M).2, Complex.I • (pairGradientCLM M).1)

def cartesianX (n : ℤ) : PotPair → ℂ :=
  gk16ScalarXModel38 sourceF betaSum n

def cartesianY (n : ℤ) : PotPair → ℂ :=
  gk16ScalarYModel38 sourceF betaSum n

/-- Global differential of the local angle, only used where the radius is nonzero. -/
def angleDerivative (n : ℤ) (φ : PotPair) : PotPair →L[ℂ] ℂ :=
  (cartesianX n φ ^ 2 + cartesianY n φ ^ 2)⁻¹ •
    (cartesianX n φ • fderiv ℂ (cartesianY n) φ -
      cartesianY n φ • fderiv ℂ (cartesianX n) φ)

def psiRootAt (n m : ℤ) (φ : PotPair) : ℂ :=
  Lib.sigmaOf (p2Extend38 n (sourceF n φ)) m

end
end NlsGge.GKDefinitionDesign

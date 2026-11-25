import Mathlib
import NlsGge.Atomic.G2.G2048
import NlsGge.ThirdConsultation.G2.G2071Support1

                                                                                                           
                                                                                                    
                                                                                    
                                                                                                                 
                                                                                                                      
                                                                     
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def normalizedChi (n m : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  (Real.pi : ℂ)*((n-m : ℤ) : ℂ)*
    psiZeta φ (p2Extend38 n (sourceF n φ)) n m z

def normalizedRemainder (n m : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  dslope (normalizedChi n m φ) (tauN φ m) z

def normalizedRootRemainderIntegral (n m : ℤ) (φ : PotPair) : ℂ :=
  (2*(Real.pi : ℂ)*Complex.I)⁻¹ *
    circleIntegral (fun z => (normalizedRoot n m φ-z)*(z-tauN φ m)/
      standardRoot φ m z * normalizedRemainder n m φ z)
      (discC φ m) (discR φ m)

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.Birkhoff.F08Bare38b
import NlsGge.Hierarchy.FiniteOrderGaussianTail38
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff

                                                                                                 
                                                                                                        
                                                                                                       
                                                                                                                 
                                                                                                       
                                                                                                       
                                                                                                                  
                                                                                                         
                                                                                               
                                                                                                          
                                                                                                           
                                                                                   
set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F
noncomputable section
open NlsGge.GKDefinitionDesign

def finiteTInv (m : ℕ) (z : Hm1 m) : Hm1 m :=
  ofCarrier38 _ (physicalSobolevFourierEquiv38 ((m - 1 : ℕ) : ℝ)
    (inverseBirkhoffSobolev (m - 1) (toCarrier38 _ z)))

def inverseOnSobolev (m : ℕ) (z : Hm1 m) : Hm1 m :=
  FinvH38 m (finiteTInv m z)

def inverseOnSequence (m : ℕ) (z : ℤ → ℂ) : Hm1 m :=
  inverseOnSobolev m (gaussianRealization38 m z)

def finiteDensity (m : ℕ) (β : ℕ → ℝ) (z : ℤ → ℂ) : ℝ :=
  Real.exp (-Rm38 m β (inverseOnSequence m z))

def finiteNormalizer (m : ℕ) (β : ℕ → ℝ) : ℝ :=
  ∫ z, finiteDensity m β z ∂gammaM38 m β

def finiteGapLaw (m : ℕ) (β : ℕ → ℝ) : Measure (Hm1 m) :=
  ((ENNReal.ofReal (finiteNormalizer m β))⁻¹ •
    (gammaM38 m β).withDensity
      (fun z => ENNReal.ofReal (finiteDensity m β z))).map
        (inverseOnSequence m)

def finiteGapField (m N : ℕ) (z : ℤ → ℂ) : Hm1 m :=
  inverseOnSobolev m (PN38 m N z)

def finiteGapNormalizer (m : ℕ) (β : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∫ z, Real.exp (-Rm38 m β (finiteGapField m N z)) ∂gammaM38 m β

def finiteGapApprox (m : ℕ) (β : ℕ → ℝ) (N : ℕ) : Measure (Hm1 m) :=
  ((ENNReal.ofReal (finiteGapNormalizer m β N))⁻¹ •
    (gammaM38 m β).withDensity
      (fun z => ENNReal.ofReal
        (Real.exp (-Rm38 m β (finiteGapField m N z))))).map
          (finiteGapField m N)

end
end NlsGge.ThirdConsultation.F

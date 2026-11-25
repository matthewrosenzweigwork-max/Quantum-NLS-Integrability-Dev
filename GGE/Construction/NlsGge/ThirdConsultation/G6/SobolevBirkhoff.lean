import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.G6.BirkhoffBasic

                                                                                                            
                                                                                                                    
                                                                                                                          
                                                                                                        
                                                                                                                      
                                                                                                               
set_option autoImplicit false
noncomputable section
open scoped Classical
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

def physicalSobolevRecover (m : ℕ) (u : PhysicalL2) :
    PhysicalSobolev38 (m : ℝ) :=
  if h : fourierSeq38 u ∈ seqSobolev38 (m : ℝ) then
    (physicalSobolevFourierEquiv38 (m : ℝ)).symm
      (carrierMk38 (m : ℝ) (fourierSeq38 u) h)
  else 0

def birkhoffSobolev (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) :
    SobolevCarrier38 (m : ℝ) :=
  let z : ℤ → ℂ := physicalBirkhoff (physicalSobolevEmbed m u)
  if h : z ∈ seqSobolev38 (m : ℝ) then
    carrierMk38 (m : ℝ) z h
  else 0

def inverseBirkhoffSobolev (m : ℕ)
    (z : SobolevCarrier38 (m : ℝ)) :
    PhysicalSobolev38 (m : ℝ) :=
  physicalSobolevRecover m
    (physicalInverseBirkhoff (sequenceSobolevEmbed m z))

def sobolevJacobianConjugate (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) :
    PhysicalSobolev38 (m : ℝ) →L[ℝ] PhysicalSobolev38 (m : ℝ) :=
  (physicalSobolevFourierEquiv38 (m : ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fderiv ℝ (birkhoffSobolev m) u)

end NlsGge.GKDefinitionDesign

end

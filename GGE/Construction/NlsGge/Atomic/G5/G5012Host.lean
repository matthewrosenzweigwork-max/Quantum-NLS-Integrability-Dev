import Mathlib
import NlsGge.Atomic.G5.G5005Host
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G6.BirkhoffBasic

                                                                                                                
                                                                                                                    
                                                                                                                            
                                                                                                                               
                                                                                                                           
                                                                                                                
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def fourierRealBasisPlus (n : ℤ) : PotPair :=
  (-1 / (Real.sqrt 2 : ℂ)) • (fourierMode 1 n + fourierMode (-1) n)

def fourierRealBasisMinus (n : ℤ) : PotPair :=
  (-1 / (Complex.I * (Real.sqrt 2 : ℂ))) •
    (fourierMode 1 n - fourierMode (-1) n)

def physicalFourierBasis (j : Bool × ℤ) : PhysicalL2 :=
  reflectedFourierL2.symm (lp.single 2 j.2 (if j.1 then 1 else Complex.I))

def physicalCoordinate (j : Bool × ℤ) (u : PhysicalL2) : ℝ :=
  if j.1 then (sourceFamily.Phi u j.2).re else (sourceFamily.Phi u j.2).im

def pairGradientProjection (v : PotPair) : PhysicalL2 := star v.1 + v.2

/-- No inversion of a noninvertible derivative occurs in this definition. -/
def jacobianConjugate (u : PhysicalL2) : PhysicalL2 →L[ℝ] PhysicalL2 :=
  (reflectedFourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
    (fderiv ℝ physicalBirkhoff u)

def jacobianAdjoint (u : PhysicalL2) : PhysicalL2 →L[ℝ] PhysicalL2 :=
  (jacobianConjugate u).adjoint

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.ThirdConsultation.I.RemainderWeight
import NlsGge.Atomic.I.I010
import NlsGge.Measure.GibbsVariational38
import NlsGge.Measure.FiniteGaussian
import NlsGge.Birkhoff.S04Moments38

                                                                                   
                                                                                              
                                                                                                                 
                                                                                                                  
                                                                                     
                                                                                                               
                                                                                                                      
                                                                                                 
                                                                        
                                                                                                              
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.I010 (spectralEnergy)

namespace NlsGge.ThirdConsultation.I

open scoped Classical in
/-- The G6 inverse, on raw coordinates. The exceptional branch is outside every
    supported sequence law used below; no second Birkhoff map is selected. -/
def physicalOfSequence (z : ℤ → ℂ) : PhysicalL2 :=
  physicalInverseBirkhoff (if h : Memℓp z 2 then ⟨z, h⟩ else 0)

def finiteGapField (Λ : Finset ℤ) (w : Λ → ℂ) : PhysicalL2 :=
  physicalOfSequence (extZero38 Λ w)

def finiteGapCoordinateLaw (W : ℝ → ℝ) (Λ : Finset ℤ) : Measure (Λ → ℂ) :=
  gibbsLaw38 (finiteComplexGaussian (fun n : Λ =>
    W (2 * Real.pi * ((n : ℤ) : ℝ))))
    (fun w => remainderForWeight W (finiteGapField Λ w))

def finiteGapLaw (W : ℝ → ℝ) (Λ : Finset ℤ) : Measure PhysicalL2 :=
  (finiteGapCoordinateLaw W Λ).map (finiteGapField Λ)

def finiteRelativeNormalizer (W : ℝ → ℝ) (Λ : Finset ℤ) : ℝ :=
  gibbsPartition38 (finiteComplexGaussian (fun n : Λ =>
    W (2 * Real.pi * ((n : ℤ) : ℝ))))
    (fun w => remainderForWeight W (finiteGapField Λ w))

def finiteAbsolutePartition (W : ℝ → ℝ) (Λ : Finset ℤ) : ℝ :=
  ∫ w : Λ → ℂ, Real.exp (-spectralEnergy W (finiteGapField Λ w))
    ∂finiteComplexVolume Λ

end NlsGge.ThirdConsultation.I

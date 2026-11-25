import Mathlib
import NlsGge.ThirdConsultation.I.FiniteGapLaws
import NlsGge.NLS38.PhysicalFlow38

                                                                                                                              
                                                                                                                      
                                                                                                                 
                                         
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

/-- The actual PDE restricted through the fixed physical coordinates. -/
def finiteGapFlow (Λ : Finset ℤ) (t : ℝ) (w : Λ → ℂ) (n : Λ) : ℂ :=
  physicalBirkhoff (NlsGge.NLS38.nlsFlowL2 t (finiteGapField Λ w)) n

end NlsGge.ThirdConsultation.I

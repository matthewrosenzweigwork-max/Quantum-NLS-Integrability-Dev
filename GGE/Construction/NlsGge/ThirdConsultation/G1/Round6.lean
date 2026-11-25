import Mathlib
import NlsGge.ThirdConsultation.G1.Round5

                                                                                                  
                                                                                        
set_option autoImplicit false
noncomputable section
open MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

def hierarchyHamiltonian (k : ℕ) (φ : PotPair) : ℂ :=
  if k=1 then ∫ x : PhysicalCircle, φ.1 x * φ.2 x ∂spatialMeasure
  else ∫ x : PhysicalCircle, φ.1 x * wkbR φ k x ∂spatialMeasure

end NlsGge.GKDefinitionDesign
end

import Mathlib
import NlsGge.ThirdConsultation.G6.Round5
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff

                                                                                                                          
                                                                                                           
                                                                                                               
                                                                                                                  
                                                                                                     
                                                         
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

def transformedNLSHamiltonian (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) : ℝ :=
  nlsHamiltonian (inverseBirkhoffSobolev 1 z)

end
end NlsGge.GKDefinitionDesign

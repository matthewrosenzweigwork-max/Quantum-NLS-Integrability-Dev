import Mathlib
import NlsGge.Atomic.G6.G6029Host
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff

                                                                                                                          
                                                                                                  
                                                                                                                   
                                                                                                                       
                                                                                                                   
                                            
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped Classical ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- The m-independent truncation is recovered in H^m only after range membership. -/
def finiteGapTruncationSobolev (m N : ℕ) (u : PhysicalL2) :
    PhysicalSobolev38 (m : ℝ) :=
  physicalSobolevRecover m (finiteGapTruncation N u)

end
end NlsGge.GKDefinitionDesign

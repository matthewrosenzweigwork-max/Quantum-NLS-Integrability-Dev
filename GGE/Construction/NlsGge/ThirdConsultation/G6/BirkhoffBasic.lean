import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.GK38.Lib.InterpolationHilbertOp

                                                                                                                         
                                                                                                                                                        
                                                                                                                                                               
                                                                                    
set_option autoImplicit false

namespace NlsGge.GKDefinitionDesign
noncomputable section
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

/-- The same physical minus representative selected in X-006. -/
def physicalBirkhoff : PhysicalL2 → Lib.L2Z := sourceFamily.Phi

/-- A total function; its inverse equations are the conclusions of G6-013. -/
def physicalInverseBirkhoff : Lib.L2Z → PhysicalL2 :=
  Function.invFun physicalBirkhoff

end
end NlsGge.GKDefinitionDesign

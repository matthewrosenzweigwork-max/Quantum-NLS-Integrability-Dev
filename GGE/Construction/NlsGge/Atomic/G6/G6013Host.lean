import Mathlib
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff

                                                                                                              
                                                                                                                        
                                                                                                                   
                                                                                                       
                                                                                           
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def inverseBirkhoffCartesian : CartesianReal → PhysicalL2 :=
  Function.invFun realBirkhoffCartesian

end
end NlsGge.GKDefinitionDesign

import NlsGge.GK38.GradFundamentalDefs

                                                                                                                  
                                                                                                             
                                                                                          
                                                                                           
set_option autoImplicit false

open NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def wedge (a b : PairVec38) : ℂ := a 0*b 1-a 1*b 0
def symmetricPair (a b : PairVec38) : ℂ := a 0*b 1+a 1*b 0
def bilinearPair (a b : PairVec38) : ℂ := a 0*b 0+a 1*b 1

end
end NlsGge.GKDefinitionDesign

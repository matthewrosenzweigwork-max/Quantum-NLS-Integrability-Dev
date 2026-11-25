import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.GK38.AbelianPsiNumerator

                                                                                                                 
                                                                                                
                                                                                     
                                                                                     
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def psi (n : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  p6PsiNumerator38 n (sourceF n) φ z

end
end NlsGge.GKDefinitionDesign

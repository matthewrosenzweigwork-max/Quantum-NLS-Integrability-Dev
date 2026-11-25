import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.GK38.AbelianPsiPeriodNormalization
import NlsGge.ThirdConsultation.G2.G2072Host

                                                                                                   
                                                                                                   
                                                                                  
                                                                                                              
                                                                                                                     
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G2_072 (φ : PotPair) (hφ : φ ∈ sourceW) (n : ℤ) :
    CircleIntegrable (fun z => psi n φ z/canonRoot38 φ z) (discC φ n) (discR φ n) ∧
    abelianPeriod38 n φ (psi n φ) = 2*(Real.pi : ℂ) :=
  p6PsiNumerator_missing_period38 n φ (sourceFamily.W_gk hφ) (sourceF n)
    (sourceFamily.F_zero n φ hφ)

end
end NlsGge.GKDefinitionDesign

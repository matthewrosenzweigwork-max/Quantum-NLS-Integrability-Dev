import NlsGge.Atomic.G1.G1070
import NlsGge.GK38.PoissonMixedDiscriminantComplete

                                                                                                         
                                                                                                           
                                                                                        
                                                                                                             
                                                                                    
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38 NlsGge.GK38.PoissonMixed38
open NlsGge.Atomic.G1070

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G1_071 (φ : PotPair) (n : ℤ) (lam : ℂ)
    (hn : simpleDirichlet φ (muSeq φ n)) :
    Q (state φ (muSeq φ n) ![1,1]) ≠ 0 ∧
    2 * kernelPoisson38 (gradDiscrimCont38 φ lam)
      (dirEigenKernel38 φ (muSeq φ n)) =
      antiDiscrim φ (muSeq φ n) * dirInterpolation38 φ (muSeq φ n) lam :=
  NlsGge.GK38.PoissonMixed38.discriminantDirichletMixedTarget φ (muSeq φ n) lam hn.1 hn.2

end
end NlsGge.GKDefinitionDesign

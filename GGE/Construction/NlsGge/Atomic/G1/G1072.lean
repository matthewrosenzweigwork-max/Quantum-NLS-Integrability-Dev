import NlsGge.Atomic.G1.G1070
import NlsGge.Atomic.G1.G1073Host
import NlsGge.GK38.PoissonMixedDiscriminantComplete

                                                                                                         
                                                                                                             
                                                                                                          
                                                                                   
                                                                                                           
                                                                                        
                                                                                                                
                                                                                                       
                                                                                                     
                                                                                               
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38 NlsGge.GK38.PoissonMixed38
open NlsGge.Atomic.G1070

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G1_072 (φ : PotPair) (n : ℤ) (lam : ℂ)
    (hlam : simplePeriodic φ lam)
    (hn : simpleDirichlet φ (muSeq φ n)) :
    deriv (discrim φ) lam ≠ 0 ∧
    2 * kernelPoisson38 (periodicKernel38 φ lam)
      (dirEigenKernel38 φ (muSeq φ n)) =
      -(antiDiscrim φ (muSeq φ n) * dirInterpolation38 φ (muSeq φ n) lam) /
        deriv (discrim φ) lam :=
  NlsGge.GK38.PoissonMixed38.periodicDirichletMixedTarget φ lam (muSeq φ n) hlam.1 hlam.2 hn.1 hn.2

end
end NlsGge.GKDefinitionDesign

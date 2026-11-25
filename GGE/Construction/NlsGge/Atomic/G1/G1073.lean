import NlsGge.Atomic.G1.G1062
import NlsGge.GK38.PoissonDirichletCommute
import NlsGge.GK38.PoissonMixedKernelAlgebra
import NlsGge.GK38.PoissonMixedPeriodicBasic
import NlsGge.Atomic.G1.G1073Host

                                                                                                         
                                                                                                                 
                                                                                                                         
                                                                                                                           
                                                                                                                           
                                                                                                                   
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38
open NlsGge.GK38.PoissonDirichlet38 NlsGge.GK38.PoissonSpectral38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G1_073 (φ : PotPair) :
    (∀ z w : ℂ, simpleDirichlet φ z → simpleDirichlet φ w →
      Q (state φ z ![1,1]) ≠ 0 ∧ Q (state φ w ![1,1]) ≠ 0 ∧
      kernelPoisson38 (dirEigenKernel38 φ z) (dirEigenKernel38 φ w) = 0) ∧
    (∀ z w : ℂ, simplePeriodic φ z → simplePeriodic φ w →
      deriv (discrim φ) z ≠ 0 ∧ deriv (discrim φ) w ≠ 0 ∧
      kernelPoisson38 (periodicKernel38 φ z) (periodicKernel38 φ w) = 0) := by
  refine ⟨fun z w hz hw => ?_, fun z w hz hw => ?_⟩
  · obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨hw1, hw2⟩ := hw
    obtain ⟨hQz, hQw, -, -, -⟩ := dirichletMutualCommuteTarget φ z w hz1 hw1 hz2 hw2
    exact ⟨hQz, hQw, kernelPoisson_dir_dir38 φ z w hz1 hw1 hz2 hw2⟩
  · obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨hw1, hw2⟩ := hw
    exact periodicMutualTarget φ z w hz1 hw1 hz2 hw2

end
end NlsGge.GKDefinitionDesign
